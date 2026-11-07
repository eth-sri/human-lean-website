// A small Lean 4 highlighter: comments, strings, keywords and declaration names.
// It works line by line, carrying block-comment state across lines.

const KEYWORDS = new Set([
  'import', 'open', 'namespace', 'section', 'end', 'noncomputable', 'private', 'protected', 'scoped',
  'variable', 'universe', 'set_option', 'attribute', 'local', 'in', 'where', 'deriving', 'extends',
  'fun', 'let', 'have', 'show', 'from', 'by', 'at', 'with', 'match', 'if', 'then', 'else', 'do', 'return',
  'calc', 'obtain', 'intro', 'intros', 'exact', 'refine', 'apply', 'rcases', 'rintro', 'simp', 'simpa',
  'rw', 'rwa', 'linarith', 'nlinarith', 'positivity', 'omega', 'norm_num', 'constructor', 'use', 'exists',
  'cases', 'induction', 'specialize', 'filter_upwards', 'gcongr', 'field_simp', 'ring', 'ring_nf', 'push_cast',
  'exact_mod_cast', 'congr', 'ext', 'funext', 'unfold', 'dsimp', 'letI', 'haveI', 'classical', 'aesop', 'grind',
  'Type', 'Prop', 'Sort',
]);
const DECLS = new Set(['theorem', 'lemma', 'def', 'abbrev', 'structure', 'class', 'inductive', 'instance', 'axiom', 'opaque', 'example']);

const esc = (s) => s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
const span = (cls, s) => `<span class="${cls}">${esc(s)}</span>`;

// Highlights one line; `state.block` is the open block-comment depth.
export function highlightLine(line, state) {
  let out = '', i = 0, expectName = false;
  while (i < line.length) {
    if (state.block > 0) {
      let j = i;
      while (j < line.length && state.block > 0) {
        if (line.startsWith('/-', j)) { state.block++; j += 2; }
        else if (line.startsWith('-/', j)) { state.block--; j += 2; }
        else j++;
      }
      out += span('tok-com', line.slice(i, j));
      i = j;
      continue;
    }
    if (line.startsWith('/-', i)) { state.block = 1; out += span('tok-com', '/-'); i += 2; continue; }
    if (line.startsWith('--', i)) {
      const rest = line.slice(i);
      out += span(/^-- HumanLean:proof_(begin|end)\s*$/.test(rest) ? 'tok-marker' : 'tok-com', rest);
      break;
    }
    const ch = line[i];
    if (ch === '"') {
      let j = i + 1;
      while (j < line.length && line[j] !== '"') j += line[j] === '\\' ? 2 : 1;
      out += span('tok-str', line.slice(i, j + 1));
      i = j + 1;
      continue;
    }
    const word = /^[A-Za-z_À-ɏͰ-Ͽἀ-῿][\w.'!?À-ɏͰ-Ͽ₀-ₜ]*/.exec(line.slice(i));
    if (word) {
      const w = word[0];
      if (expectName) { out += span('tok-decl', w); expectName = false; }
      else if (DECLS.has(w)) { out += span('tok-kw', w); expectName = true; }
      else if (KEYWORDS.has(w)) out += span('tok-kw', w);
      else out += esc(w);
      i += w.length;
      continue;
    }
    out += esc(ch);
    i++;
  }
  return out;
}

export function highlight(text) {
  const state = { block: 0 };
  return text.split('\n').map((l) => highlightLine(l, state)).join('\n');
}
