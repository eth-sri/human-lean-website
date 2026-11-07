// Benchmark charts, from the aggregate results in the paper.
// Two series throughout: the raw agent (--raw) and HumanLean (--ours),
// grouped by model. Columns are HTML so labels reflow on narrow screens.
import { h, fmt } from './util.js';

const SYSTEMS = [['baseline', 'Raw agent', 'raw'], ['ours', 'HumanLean', 'ours']];
const MODEL_ORDER = ['sol', 'astra'];
const round2 = (x) => Math.round(x * 100) / 100;

function find(bench, system, model) {
  return bench.aggregate.find((r) => r.system === system && r.model === model);
}

// A column chart panel on a shared zero baseline. groups: [{ name, cols: [{ cls,
// value, label, delta?, reduction?, aria }] }]; labels sit above column tops.
export function columnPanel(title, max, groups) {
  return h('div', { class: 'chart-panel' }, h('h4', {}, title), h('div', { class: 'cols' }, groups.map((g) =>
    h('div', { class: 'col-group' },
      h('div', { class: 'plot' }, g.cols.map((c) => {
        const pct = `${Math.max(0, Math.min(1, c.value / max)) * 100}%`;
        return h('div', { class: `col ${c.cls}`, role: 'img', 'aria-label': c.aria },
          h('div', { class: 'fill', style: { height: pct } }),
          h('div', { class: 'val', style: { bottom: pct } }, c.label, c.delta ? h('span', { class: 'delta' }, c.delta) : null),
          c.reduction ? h('span', {
            class: 'reduction', 'aria-hidden': 'true',
            style: {
              bottom: `calc(${pct} + 2rem)`,
              height: `calc(${100 * (c.reduction.rawValue - c.value) / max}% + 1rem)`,
            },
          }, h('strong', {}, c.reduction.label)) : null);
      })),
      h('div', { class: 'g' }, g.name)))));
}

// Per model, the raw agent and HumanLean side by side.
function panel({ title, bench, value, max, label, reduction }) {
  return columnPanel(title, max, MODEL_ORDER.map((model) => {
    return {
      name: bench.models[model],
      cols: SYSTEMS.map(([system, name, cls]) => {
        const v = value(find(bench, system, model));
        const comparison = system === 'ours' && reduction ? {
          label: reduction(model), rawValue: value(find(bench, 'baseline', model)),
        } : null;
        return {
          cls, value: v, label: label(v), reduction: comparison,
          aria: `${bench.models[model]}, ${name}: ${label(v)}${comparison ? `, ${comparison.label} than raw agent` : ''}`,
        };
      }),
    };
  }));
}

export function renderFaithfulness(host, bench) {
  host.replaceChildren(
    panel({
      title: 'Faithfulness', bench, max: 100,
      value: (r) => (100 * r.faithful) / r.formalized,
      label: (v) => `${fmt(v, 1)}%`,
    }));
}

export function renderComplexity(host, bench) {
  const perFM = (key) => (r) => round2(r[key] / r.formalized);
  const metric = (title, key) => {
    const max = Math.max(...bench.aggregate.map(perFM(key)));
    return panel({
      title, bench, max,
      value: perFM(key),
      label: (v) => fmt(v, 2),
      reduction: (model) => {
        const raw = find(bench, 'baseline', model);
        const ours = find(bench, 'ours', model);
        // Compute from unrounded per-goal counts, not the displayed values.
        const ratio = (ours[key] / ours.formalized) / (raw[key] / raw.formalized);
        return `${Math.round(100 * (1 - ratio))}% fewer`;
      },
    });
  };
  host.replaceChildren(
    metric('Definitions', 'defs'),
    metric('Axioms', 'axioms'),
    metric('Duplicates', 'duplicates'));
}
