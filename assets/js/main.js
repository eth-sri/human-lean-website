// Page entry: fills the data-driven parts.
import { getJSON } from './util.js';
import { renderFaithfulness, renderComplexity } from './charts.js?v=verbosity1';
import { renderUnitDistance } from './unit-distance.js';

const fail = (host, err) => {
  console.error(err);
  host.textContent = 'Could not load the data for this section.';
  host.classList.add('muted');
};

getJSON('data/benchmark.json').then((bench) => {
  const faithfulness = document.getElementById('chart-faithfulness');
  if (faithfulness) renderFaithfulness(faithfulness, bench);
  renderComplexity(document.getElementById('chart-complexity'), bench);
}).catch((e) => fail(document.getElementById('chart-complexity'), e));

Promise.all([getJSON('data/unit-distance/manifest.json'), getJSON('data/unit-distance/comparison.json')])
  .then(([ud, comparison]) => {
    renderUnitDistance(ud, comparison);
    // Notes are created asynchronously, after the initial hash-navigation pass.
    if (location.hash.startsWith('#ud-note-')) {
      revealTarget(location.hash);
      document.getElementById(location.hash.slice(1))?.scrollIntoView();
    }
  })
  .catch((e) => fail(document.getElementById('file-count'), e));

// Anchor navigation also reveals folded targets.
function revealTarget(hash) {
  const target = document.getElementById(hash.slice(1));
  for (let el = target; el; el = el.parentElement) {
    if (el.tagName === 'DETAILS') el.open = true;
  }
}
document.addEventListener('click', (event) => {
  const link = event.target.closest('a[href^="#"]');
  if (link) revealTarget(link.hash);
});
window.addEventListener('hashchange', () => revealTarget(location.hash));
revealTarget(location.hash);

// Make horizontal figure scrolling explicit across browser keyboard bindings.
for (const frame of document.querySelectorAll('.figure-frame')) {
  frame.addEventListener('keydown', (event) => {
    if (event.altKey || event.ctrlKey || event.metaKey || event.shiftKey) return;
    if (event.key !== 'ArrowLeft' && event.key !== 'ArrowRight') return;
    event.preventDefault();
    frame.scrollBy({ left: event.key === 'ArrowRight' ? 80 : -80 });
  });
}

const sectionLinks = [...document.querySelectorAll('.section-nav a')];
const sections = sectionLinks.map((link) => document.getElementById(link.hash.slice(1)));
const sidebarToggle = document.querySelector('.sidebar-toggle');
const compactSidebar = matchMedia('(max-width:767px)');
function closeSidebar() {
  sidebarToggle.setAttribute('aria-expanded', 'false');
}
sidebarToggle.addEventListener('click', () => {
  sidebarToggle.setAttribute('aria-expanded', sidebarToggle.getAttribute('aria-expanded') !== 'true');
});
for (const link of sectionLinks) {
  link.addEventListener('click', () => {
    if (!compactSidebar.matches) return;
    closeSidebar();
    const heading = document.querySelector(`${link.hash} h2`);
    heading.setAttribute('tabindex', '-1');
    requestAnimationFrame(() => heading.focus({ preventScroll: true }));
  });
}
document.addEventListener('keydown', (event) => {
  if (event.key === 'Escape' && sidebarToggle.getAttribute('aria-expanded') === 'true') {
    closeSidebar();
    sidebarToggle.focus({ preventScroll: true });
  }
});
compactSidebar.addEventListener('change', closeSidebar);

let scrollPending = false;
function updateSection() {
  let active = 0;
  sections.forEach((section, index) => {
    if (section.getBoundingClientRect().top <= innerHeight * 0.35) active = index;
  });
  if (Math.ceil(scrollY + innerHeight) >= document.documentElement.scrollHeight) {
    // A short final section can clamp an earlier anchor at the page bottom.
    const linked = sections.findIndex((section) => `#${section.id}` === location.hash);
    if (linked === sections.length - 1 || linked !== active) active = sections.length - 1;
  }
  // Honor a linked section at its native anchor position, even when it is short.
  const linked = sections.findIndex((section) => `#${section.id}` === location.hash);
  if (linked >= 0) {
    const section = sections[linked];
    const margin = parseFloat(getComputedStyle(section).scrollMarginTop) || 0;
    const anchorY = Math.max(0, Math.min(
      scrollY + section.getBoundingClientRect().top - margin,
      document.documentElement.scrollHeight - innerHeight,
    ));
    if (Math.abs(scrollY - anchorY) <= 2) active = linked;
  }
  sectionLinks.forEach((link, index) => {
    if (index === active) link.setAttribute('aria-current', 'location');
    else link.removeAttribute('aria-current');
  });
  scrollPending = false;
}
function scheduleSectionUpdate() {
  if (!scrollPending) {
    scrollPending = true;
    requestAnimationFrame(updateSection);
  }
}
window.addEventListener('scroll', scheduleSectionUpdate, { passive: true });
window.addEventListener('resize', scheduleSectionUpdate);
window.addEventListener('load', scheduleSectionUpdate);
window.addEventListener('hashchange', scheduleSectionUpdate);
updateSection();
