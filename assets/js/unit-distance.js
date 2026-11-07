// Browser for the published unit-distance formalization (site/data/unit-distance/).
import { h, fmt, getJSON } from './util.js';
import { highlightLine } from './lean.js';
import { helperProofRanges, markedProofRanges } from './proof-fold.js';

const BASE = 'data/unit-distance/';
const ROLE_COLORS = {
  entry: 'var(--role-review)',
  definitions: 'var(--role-review)',
  axioms: 'var(--role-axiom)',
  result: 'var(--role-result)',
  helper: 'var(--role-helper)',
};
const ORDER = ['entry', 'definitions', 'axioms', 'result', 'helper'];
const naturalOrder = new Intl.Collator('en', { numeric: true });

function comparePaperReferences(a, b) {
  // Labels use 2.3; result filenames and helper directories encode it as 2p3.
  const reference = (text) => text.match(/(?:^|[\s_/])((?:\d+|[A-Z])(?:[.p]\d+)+)(?=$|[/.])/i)?.[1].replace(/p(?=\d)/gi, '.') ?? text;
  return naturalOrder.compare(reference(a), reference(b)) || naturalOrder.compare(a, b);
}

export function renderUnitDistance(ud, comparison) {
  const colors = {
    definitions: 'var(--role-review)', axioms: 'var(--role-axiom)',
    numbered_results: 'var(--role-result)', helpers: 'var(--role-helper)', outside: 'var(--faint)',
  };
  const categories = comparison.category_order;
  const rows = Object.values(comparison.artifacts);
  const subtotal = (row) => comparison.plot.subtotal_categories.reduce((sum, key) => sum + row.categories[key], 0);
  const max = Math.max(...rows.map(subtotal));
  const outsideCapacity = max * comparison.plot.outside_capacity_ratio;
  const compression = (row) => Math.max(1, row.categories.outside / outsideCapacity);
  const note = (n) => h('sup', {}, h('a', { href: `#ud-note-${n}`, 'aria-label': `Footnote ${n}` }, `[${n}]`));
  const rowName = (row) => row.name;
  const categoryLabel = (key) => [comparison.labels[key],
    { definitions: 1, axioms: 2, outside: 3 }[key] ? note({ definitions: 1, axioms: 2, outside: 3 }[key]) : null];
  const countRow = (label, counts, className) => h('tr', { class: className }, h('th', { scope: 'row' }, label), counts.map((count) => h('td', {}, count)));
  const categoryRow = (key) => countRow(
    [h('i', { class: 'swatch', 'aria-hidden': 'true', style: { background: colors[key] } }), ' ', categoryLabel(key)],
    rows.map((row) => [fmt(row.categories[key]), key === 'axioms' && row.note ? note(row.note) : null]));
  document.getElementById('ud-size').replaceChildren(h('figure', { class: 'source-size-chart' },
    h('figcaption', {}, 'Lines of Lean code, excluding all comments and blanks.'),
    // LoC bar plot temporarily disabled; keep the exact-count table below.
    // rows.map((row) => h('div', { class: 'source-size-row' },
    //   h('p', { class: 'source-size-label' }, h('strong', {}, rowName(row)),
    //     h('span', {}, `${fmt(row.files)} Lean files`)),
    //   h('div', {
    //     class: 'source-size-plot', role: 'img',
    //     style: { gridTemplateColumns: `minmax(0,1fr) auto minmax(0,${comparison.plot.outside_capacity_ratio}fr)` },
    //     'aria-label': `${row.name}: ${categories.map((key) => `${comparison.labels[key]}: ${fmt(row.categories[key])} lines`).join('. ')}. Subtotal ${fmt(subtotal(row))}, excluding external/background code. Full total ${fmt(row.line_total)}. ${compression(row) > 1 ? `External segment compressed ${fmt(compression(row), 1)} times.` : 'No compressed segment.'}`,
    //   },
    //   h('div', { class: 'source-size-track' }, categories.filter((key) => key !== 'outside').map((key) => h('span', {
    //     class: 'source-size-segment',
    //     style: { width: `${100 * row.categories[key] / max}%`, background: colors[key] },
    //     title: `${comparison.labels[key]}: ${fmt(row.categories[key])} lines of Lean code`,
    //   }))),
    //   h('span', { class: 'source-size-break', 'aria-hidden': 'true', style: { visibility: compression(row) > 1 ? 'visible' : 'hidden' } }, '//'),
    //   h('div', { class: 'source-size-track' }, h('span', {
    //     class: 'source-size-segment', 'data-compression-factor': compression(row),
    //     style: { width: `${100 * Math.min(row.categories.outside / outsideCapacity, 1)}%`, background: colors.outside },
    //     title: `External/background & other: ${fmt(row.categories.outside)} lines of Lean code${compression(row) > 1 ? ` (compressed ${fmt(compression(row), 1)}×)` : ' (linear scale)'}`,
    //   }))))),
    h('div', { class: 'source-size-table', tabindex: '0', role: 'region', 'aria-label': 'Lines of Lean code by category' },
      h('table', { class: 'source-size-counts', 'aria-label': 'Lines of Lean code by category' },
        h('thead', {}, h('tr', {}, h('th', { scope: 'col' }, 'Category'), rows.map((row) => h('th', { scope: 'col' }, rowName(row))))),
        h('tbody', {}, comparison.plot.subtotal_categories.map(categoryRow),
        countRow('Subtotal', rows.map((row) => [fmt(subtotal(row)), row.subtotal_note ? note(row.subtotal_note) : null]), 'source-size-subtotal'),
        categoryRow('outside'),
        countRow('Total lines', rows.map((row) => fmt(row.line_total)), 'source-size-subtotal')))),
    h('details', { class: 'more', id: 'ud-notes' },
      h('summary', {}, 'Notes'),
      h('div', { class: 'disclosure-body' },
        h('ol', { class: 'source-size-notes' }, comparison.notes.map((item) =>
          h('li', { id: `ud-note-${item.number}`, tabindex: '-1' }, item.parts.map((part) =>
            typeof part === 'string' ? part : part.code ? h('code', {}, part.code) :
              h('a', { href: part.url, target: '_blank', rel: 'noopener' }, part.text)))))))));
  renderExplorer(ud);
}

function renderExplorer(ud) {
  const tree = document.getElementById('tree');
  const code = document.querySelector('#viewer-code code');
  const pathEl = document.getElementById('viewer-path');
  const roleEl = document.getElementById('viewer-role');
  const fold = document.getElementById('fold-proofs');
  const cache = new Map();
  const explorer = document.getElementById('explorer');
  const paper = document.getElementById('paper-statement');
  const paperBody = document.getElementById('paper-statement-body');
  let current = null;
  let paperData = null;
  let paperError = false;

  function showPaper(f) {
    const isResult = f.role === 'result';
    paper.hidden = !isResult;
    explorer.classList.toggle('has-statement', isResult);
    if (!isResult) { paperBody.replaceChildren(); return; }
    if (paperError) {
      paperBody.replaceChildren(h('p', {}, 'Paper statements could not be loaded.'),
        h('button', { type: 'button', onclick: loadPaper }, 'Retry'));
      return;
    }
    if (!paperData) { paperBody.textContent = 'Loading paper statement…'; return; }
    const statement = paperData.statements[f.label];
    if (!statement) { paperBody.textContent = 'No paper statement is mapped to this result.'; return; }
    const ready = typeof window.katex?.render === 'function'
      && typeof window.renderMathInElement === 'function'
      && document.getElementById('statement-math-css')?.sheet;
    const formatted = ready && Array.isArray(statement.latex_paragraphs)
      && statement.latex_paragraphs.length === statement.paragraphs.length
      && (!statement.formula || typeof statement.latex_formula === 'string');
    const fill = (math) => {
      const formula = statement.formula ? h('p', { class: 'paper-formula' }, math ? '' : statement.formula) : null;
      paperBody.replaceChildren(
        h('p', {}, h('strong', {}, f.label)),
        ...(math ? statement.latex_paragraphs : statement.paragraphs).map((text) => h('p', {}, text)),
        ...(formula ? [formula] : []),
        h('p', { class: 'paper-source' }, 'Paraphrase · ', h('a', {
          href: `${paperData.source.url}#page=${statement.page}`, target: '_blank', rel: 'noopener',
        }, `OpenAI PDF, p. ${statement.page}`)));
      return formula;
    };
    let rendered = false;
    if (formatted) {
      // Fresh macros per selection; HTML/resource commands are never trusted.
      const options = { trust: false, strict: 'error', throwOnError: true,
        maxSize: 10, maxExpand: 1000, macros: {}, output: 'htmlAndMathml' };
      const formula = fill(true);
      let failed = false;
      try {
        window.renderMathInElement(paperBody, { ...options,
          delimiters: [{ left: '\\(', right: '\\)', display: false }],
          errorCallback: () => { failed = true; } });
        if (formula) window.katex.render(statement.latex_formula, formula, { ...options, displayMode: true });
        rendered = !failed;
      } catch { /* Readable source-grounded notation remains available below. */ }
    }
    if (!rendered) {
      fill(false);
      paperBody.append(h('p', { class: 'figure-note', role: 'status' },
        'Math typesetting unavailable. Showing readable notation.'));
    }
    paper.scrollTop = 0;
  }

  async function loadPaper() {
    paperError = false;
    if (current) showPaper(current);
    try {
      const data = await getJSON(BASE + 'statements.json');
      if (!data.source?.url || !data.statements) throw new Error('Invalid statement data');
      paperData = data;
    } catch { paperError = true; }
    if (current) showPaper(current);
  }

  // Directory tree, top-level files first in review order, helpers last.
  const root = { dirs: new Map(), files: [] };
  for (const f of ud.files) {
    const parts = f.path.split('/');
    let node = root;
    for (const d of parts.slice(0, -1)) {
      if (!node.dirs.has(d)) node.dirs.set(d, { dirs: new Map(), files: [] });
      node = node.dirs.get(d);
    }
    node.files.push(f);
  }
  const buttons = new Map();
  const list = (node) => h('ul', {},
    node.files.sort((a, b) => ORDER.indexOf(a.role) - ORDER.indexOf(b.role) || comparePaperReferences(a.label || a.path, b.label || b.path)).map((f) => {
      const name = f.path.split('/').pop();
      const b = h('button', { type: 'button', title: f.path, onclick: () => open(f) },
        h('i', { style: { background: ROLE_COLORS[f.role] } }), h('span', { class: 'file-name' }, name), h('span', { class: 'n' }, '…'));
      buttons.set(f.path, b);
      return h('li', {}, b);
    }),
    [...node.dirs].sort(([a], [b]) => comparePaperReferences(a, b)).map(([d, child]) => h('li', {}, h('div', { class: 'dir' }, `${d}/`), list(child))));
  tree.replaceChildren(list(root));

  const filter = document.getElementById('file-filter');
  const count = document.getElementById('file-count');
  function filterFiles() {
    const query = filter.value.trim().toLowerCase();
    let shown = 0;
    for (const [path, button] of buttons) {
      const matches = path.toLowerCase().includes(query);
      button.parentElement.hidden = !matches;
      if (matches) shown++;
    }
    // Hide empty directories from the leaves upward.
    for (const ul of [...tree.querySelectorAll('ul')].reverse()) {
      if (ul.parentElement.tagName === 'LI') {
        ul.parentElement.hidden = ![...ul.children].some((li) => !li.hidden);
      }
    }
    count.textContent = shown ? `${shown} of ${ud.files.length} files` : 'No matching files';
  }
  filter.addEventListener('input', filterFiles);
  filterFiles();

  function load(f) {
    if (!cache.has(f.path)) {
      const request = fetch(BASE + 'files/' + f.path).then(async (res) => {
        if (!res.ok) throw new Error(`Source: ${res.status}`);
        const text = await res.text();
        const lines = f.code_lines;
        if (!Number.isInteger(lines) || lines < 0) throw new Error('Audited code-line count unavailable');
        const button = buttons.get(f.path);
        button.querySelector('.n').textContent = `${fmt(lines)} lines`;
        button.title = `${f.path} · ${fmt(lines)} lines of Lean code`;
        return text;
      }).catch((error) => {
        cache.delete(f.path);
        buttons.get(f.path).querySelector('.n').textContent = 'Unavailable';
        throw error;
      });
      cache.set(f.path, request);
    }
    return cache.get(f.path);
  }

  async function open(f) {
    current = f;
    for (const [p, b] of buttons) b.setAttribute('aria-current', String(p === f.path));
    pathEl.textContent = f.path;
    roleEl.textContent = f.label ? `· ${f.label}` : '';
    code.textContent = 'Loading source…';
    showPaper(f);
    try {
      const text = await load(f);
      if (current === f) render(text);
    } catch {
      if (current === f) code.textContent = 'Source file could not be loaded. Select it again to retry.';
    }
  }

  // Marked result proofs and individual helper proofs collapse independently.
  function render(text) {
    const lines = text.replace(/\n$/, '').split('\n');
    const state = { block: 0 };
    const out = [];
    const ranges = !fold.checked ? [] : current.role === 'result' ? markedProofRanges(text)
      : current.role === 'helper' ? helperProofRanges(text) : [];
    let rangeIndex = 0;
    lines.forEach((line, i) => {
      const n = i + 1;
      const highlighted = highlightLine(line, state);
      const range = ranges[rangeIndex];
      if (range && n >= range.start && n <= range.end) {
        const bodyLines = range.end - range.start + 1 - (current.role === 'result' ? 2 : 0);
        if (n === range.start) out.push(`<span class="ln folded" data-n="${n}">  ⋯ proof, ${bodyLines} source lines</span>`);
        if (n === range.end) rangeIndex++;
        return;
      }
      out.push(`<span class="ln" data-n="${n}">${highlighted || ' '}</span>`);
    });
    code.innerHTML = out.join('');
    code.parentElement.scrollTop = 0;
  }

  for (const link of document.querySelectorAll('a[data-file]')) {
    const file = ud.files.find((f) => f.path === link.dataset.file);
    if (file) link.addEventListener('click', () => open(file));
  }

  fold.addEventListener('change', () => {
    const file = current;
    if (file) load(file).then((text) => { if (current === file) render(text); }).catch(() => {});
  });
  // Reuse source requests for exact displayed counts and later file selection.
  for (const file of ud.files) load(file).catch(() => {});
  loadPaper();
  window.addEventListener('load', () => { if (current) showPaper(current); }, { once: true });
  open(ud.files.find((f) => f.role === 'entry') ?? ud.files[0]);
}
