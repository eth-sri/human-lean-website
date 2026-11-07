const ambiguousHeader = /(?:^|[^\w'.])(?:letI?|have|by|show|suffices)\b/;

// Lexical masking preserves columns and source lines; it never rewrites Lean.
function scanLines(text) {
  let block = 0, quote = '', unsupported = false;
  const stack = [];
  const pairs = { ')': '(', ']': '[', '}': '{', '⟩': '⟨', '⦄': '⦃' };
  const lines = text.split('\n').map((raw) => {
    const opaque = block > 0 || quote !== '';
    const depth = stack.length;
    let code = '', doc = false;
    for (let i = 0; i < raw.length;) {
      if (block) {
        if (raw.startsWith('/-', i)) { block++; code += '  '; i += 2; }
        else if (raw.startsWith('-/', i)) { block--; code += '  '; i += 2; }
        else { code += ' '; i++; }
      } else if (quote) {
        if (quote === '"' && raw[i] === '\\') {
          code += '  '; i += 2;
        } else {
          if (raw[i] === quote) quote = '';
          code += ' '; i++;
        }
      } else if (raw.startsWith('--', i)) {
        code += ' '.repeat(raw.length - i); break;
      } else if (raw.startsWith('/-', i)) {
        doc ||= /^\/-[-!]/.test(raw.slice(i));
        block = 1; code += '  '; i += 2;
      } else if (raw[i] === '"' || raw[i] === '«') {
        quote = raw[i] === '«' ? '»' : '"';
        code += 'x'; i++;
      } else {
        // Character literals, unlike identifier primes, can contain delimiters.
        const char = raw[i] === "'" && /^'(?:\\(?:u\{[0-9a-fA-F]+\}|.)|[^'\\])'/u.exec(raw.slice(i));
        if (char) { code += 'x'.repeat(char[0].length); i += char[0].length; }
        else {
          // Quotations and raw strings need a richer lexer: fail open for display.
          if (raw[i] === '`' || /^r#*"/.test(raw.slice(i))) unsupported = true;
          code += raw[i++];
        }
      }
    }
    const assigns = [];
    let colon = false, top = '';
    for (let i = 0; i < code.length; i++) {
      const ch = code[i];
      if ('([{⟨⦃'.includes(ch)) { stack.push(ch); top += ' '; }
      else if (Object.hasOwn(pairs, ch)) {
        if (stack.pop() !== pairs[ch]) unsupported = true;
      } else if (!stack.length) {
        if (ch === ':') {
          if (code[i + 1] === '=') assigns.push({ index: i, colon, ambiguous: ambiguousHeader.test(top) });
          else if (code[i + 1] !== ':' && code[i - 1] !== ':') colon = true;
        }
        top += ch;
      }
    }
    return { raw, code, opaque, depth, doc, assigns, colon,
      ambiguous: ambiguousHeader.test(top), endDepth: stack.length, open: block > 0 || quote !== '' };
  });
  return unsupported || block || quote || stack.length ? [] : lines;
}

const declaration = /^(?:(?:private|protected)\s+)*(?:theorem|lemma)\s+[A-Za-z_][\w'.]*(?=\s|[:({\[]|$)/;
const command = /^(?:(?:private|protected|noncomputable|local|scoped)\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|coinductive|axiom|opaque|example|end|namespace|section|variable|variables|universe|universes|open|export|import|attribute|set_option|syntax|macro|elab|notation|infixl?|infixr|prefix|postfix|mutual|where|deriving)\b/;

/** Return paired HumanLean proof-marker ranges, including the marker lines. */
export function markedProofRanges(text) {
  const ranges = [];
  let start = null;
  for (const [i, line] of scanLines(text).entries()) {
    if (line.opaque) continue;
    const marker = /^\s*-- HumanLean:proof_(begin|end)\s*$/.exec(line.raw);
    if (!marker) continue;
    // Malformed marker pairs leave the complete source visible.
    if (marker[1] === 'begin') {
      if (start !== null) return [];
      start = i + 1;
    } else {
      if (start === null) return [];
      ranges.push({ start, end: i + 1 });
      start = null;
    }
  }
  return start === null ? ranges : [];
}

/** Return ordered, disjoint 1-based inclusive helper proof-body line ranges. */
export function helperProofRanges(text) {
  // PIRA: unindented, plain-named theorem/lemma declarations with a multiline
  // proof. Simple one-line let/letI values in the statement are retained.
  // Ambiguous headers, inline proofs, quotations and raw strings stay visible;
  // richer Lean syntax would require a parser, not broader heuristics.
  const lines = scanLines(text);
  const ranges = [];
  for (let i = 0; i < lines.length; i++) {
    const first = lines[i];
    if (first.opaque || first.depth || !declaration.test(first.code)) continue;
    let header = i, colon = false, ambiguous = false, found = false;
    for (; header < lines.length; header++) {
      const line = lines[header];
      if (header > i && !line.opaque && line.raw.trim() && !/^\s/.test(line.raw)) break;
      if (line.doc || (header > i && command.test(line.code.trimStart()))) break;
      if (line.assigns.length) {
        const assign = line.assigns[0];
        const prefix = line.code.slice(0, assign.index).trim();
        if (/^letI?\b/.test(prefix)) {
          // A statement-local binding is not the declaration's proof assignment.
          // Accept only a complete, balanced single-line value; a tactic value
          // could otherwise hide the remainder of the statement.
          const value = line.code.slice(assign.index + 2).trim();
          if (!colon || line.depth || line.endDepth || line.open ||
              line.assigns.length !== 1 || !value || ambiguousHeader.test(value) ||
              /(?:=>|[=+*/,:;])\s*$/.test(value)) break;
          continue;
        }
        found = (colon || assign.colon) && !ambiguous && !assign.ambiguous && !line.open &&
          /^:=(?:\s+by)?\s*$/.test(line.code.slice(assign.index));
        break;
      }
      colon ||= line.colon;
      ambiguous ||= line.ambiguous;
    }
    if (!found) continue;
    let end = header;
    for (let j = header + 1; j < lines.length; j++) {
      const line = lines[j];
      if (!line.opaque && (line.doc ||
          (line.raw.trim() && !/^\s/.test(line.raw)) ||
          command.test(line.code.trimStart()) || line.code.trimStart().startsWith('@['))) break;
      // Keep trailing whitespace and comment-only lines visible.
      if (line.code.trim()) end = j;
    }
    if (end > header) {
      ranges.push({ start: header + 2, end: end + 1 });
      i = end;
    }
  }
  return ranges;
}
