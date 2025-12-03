/* js/tools.js
   Single-panel, lazy-init toolkit. Full algorithms included for FIRST/FOLLOW,
   Left Recursion elimination, Left Factoring, LL(1) checks, and Regex tester.
*/

/* ---------- tiny UI helpers ---------- */
function toast(msg, time = 1600) {
  let c = document.getElementById('__toast_container');
  if (!c) {
    c = document.createElement('div'); c.id = '__toast_container';
    c.style.position = 'fixed'; c.style.right = '18px'; c.style.bottom = '18px'; c.style.zIndex = 9999;
    document.body.appendChild(c);
  }
  const el = document.createElement('div');
  el.textContent = msg; el.style.background = '#111'; el.style.color = '#fff';
  el.style.padding = '8px 12px'; el.style.marginTop = '8px'; el.style.borderRadius = '8px'; el.style.opacity = '1';
  el.style.fontSize = '13px';
  c.appendChild(el);
  setTimeout(()=>{ el.style.transition='all .28s'; el.style.opacity = '0'; el.style.transform='translateX(30px)'; setTimeout(()=>el.remove(),280); }, time);
}
function downloadText(name, text) {
  const a = document.createElement('a'); a.href = URL.createObjectURL(new Blob([text], { type: 'text/plain' }));
  a.download = name; document.body.appendChild(a); a.click(); a.remove();
}
function copyToClipboard(text) {
  if (!navigator.clipboard) { toast('Clipboard not available'); return; }
  navigator.clipboard.writeText(text).then(()=>toast('Copied to clipboard'), ()=>toast('Copy failed'));
}

/* ---------- shared grammar helpers ---------- */
function parseGrammar(text) {
  const lines = text.split('\n').map(s => s.trim()).filter(Boolean);
  const prods = {};
  for (const line of lines) {
    const idx = line.indexOf('->'); if (idx === -1) continue;
    const lhs = line.slice(0, idx).trim();
    const rhsText = line.slice(idx + 2).trim();
    const alts = rhsText.split('|').map(x => x.trim()).filter(Boolean);
    if (!prods[lhs]) prods[lhs] = [];
    for (const alt of alts) {
      const toks = alt === '' ? ['ε'] : alt.split(/\s+/).map(t => t === 'epsilon' ? 'ε' : t);
      prods[lhs].push(toks.length ? toks : ['ε']);
    }
  }
  return prods;
}
function stringifyGrammar(prods) {
  const keys = Object.keys(prods);
  const lines = [];
  for (const k of keys) {
    const rhss = prods[k].map(r => r.join(' '));
    lines.push(`${k} -> ${rhss.join(' | ')}`);
  }
  return lines.join('\n');
}
function identifySymbols(prods) {
  const nonterminals = new Set(Object.keys(prods));
  const terminals = new Set();
  for (const [A, rhss] of Object.entries(prods)) {
    for (const rhs of rhss) {
      for (const tok of rhs) {
        if (tok === 'ε') continue;
        if (!nonterminals.has(tok)) terminals.add(tok);
      }
    }
  }
  return { nonterminals: Array.from(nonterminals), terminals: Array.from(terminals) };
}

/* ---------- FIRST & FOLLOW ---------- */
function computeFirst(prods) {
  const FIRST = {}; for (const A of Object.keys(prods)) FIRST[A] = new Set();
  let changed = true;
  while (changed) {
    changed = false;
    for (const [A, rhss] of Object.entries(prods)) {
      for (const rhs of rhss) {
        let nullablePrefix = true;
        for (const sym of rhs) {
          if (sym === 'ε') { if (!FIRST[A].has('ε')) { FIRST[A].add('ε'); changed = true; } nullablePrefix = false; break; }
          if (!prods[sym]) { if (!FIRST[A].has(sym)) { FIRST[A].add(sym); changed = true; } nullablePrefix = false; break; }
          for (const t of FIRST[sym]) if (t !== 'ε' && !FIRST[A].has(t)) { FIRST[A].add(t); changed = true; }
          if (!FIRST[sym].has('ε')) { nullablePrefix = false; break; }
        }
        if (nullablePrefix) { if (!FIRST[A].has('ε')) { FIRST[A].add('ε'); changed = true; } }
      }
    }
  }
  const out = {}; for (const [k, s] of Object.entries(FIRST)) out[k] = Array.from(s);
  return out;
}
function computeFollow(prods, FIRST, start) {
  const follow = {}; for (const A of Object.keys(prods)) follow[A] = new Set();
  follow[start].add('$');
  let changed = true;
  while (changed) {
    changed = false;
    for (const [A, rhss] of Object.entries(prods)) {
      for (const rhs of rhss) {
        for (let i = 0; i < rhs.length; i++) {
          const B = rhs[i];
          if (!prods[B]) continue;
          let firstBeta = new Set(), betaNullable = true;
          for (let j = i + 1; j < rhs.length; j++) {
            const s = rhs[j];
            if (s === 'ε') { firstBeta.add('ε'); betaNullable = true; break; }
            if (!prods[s]) { firstBeta.add(s); betaNullable = false; break; }
            for (const t of FIRST[s]) if (t !== 'ε') firstBeta.add(t);
            if (!FIRST[s].includes('ε')) { betaNullable = false; break; }
          }
          if (i === rhs.length - 1) betaNullable = true;
          for (const t of firstBeta) if (t !== 'ε' && !follow[B].has(t)) { follow[B].add(t); changed = true; }
          if (betaNullable) { for (const t of follow[A]) if (!follow[B].has(t)) { follow[B].add(t); changed = true; } }
        }
      }
    }
  }
  const out = {}; for (const [k, s] of Object.entries(follow)) out[k] = Array.from(s);
  return out;
}
function prettySetsHTML(obj) {
  let html = `<table class="sets"><thead><tr><th>Symbol</th><th>Set</th></tr></thead><tbody>`;
  const keys = Object.keys(obj).sort();
  for (const k of keys) html += `<tr><td><strong>${k}</strong></td><td>${(obj[k]||[]).join(', ') || '—'}</td></tr>`;
  html += `</tbody></table>`;
  return html;
}

/* ---------- Left recursion elimination ---------- */
function eliminateLeftRecursion(originalProds) {
  const prods = {}; for (const k of Object.keys(originalProds)) prods[k] = originalProds[k].map(x => x.slice());
  const nonterminals = Object.keys(prods);
  for (let i = 0; i < nonterminals.length; i++) {
    const Ai = nonterminals[i];
    for (let j = 0; j < i; j++) {
      const Aj = nonterminals[j];
      const newRHS = [];
      for (const rhs of prods[Ai]) {
        if (rhs[0] === Aj) {
          for (const delta of prods[Aj]) {
            const combined = (delta.length === 1 && delta[0] === 'ε') ? rhs.slice(1) : delta.concat(rhs.slice(1));
            newRHS.push(combined.length ? combined : ['ε']);
          }
        } else newRHS.push(rhs);
      }
      prods[Ai] = newRHS;
    }
    const alphas = [], betas = [];
    for (const rhs of prods[Ai]) {
      if (rhs[0] === Ai) { const rest = rhs.slice(1); alphas.push(rest.length ? rest : ['ε']); }
      else betas.push(rhs);
    }
    if (alphas.length > 0) {
      let prime = Ai + "'"; while (prods[prime]) prime += "'";
      prods[prime] = [];
      const newAi = [];
      for (const b of betas) newAi.push((b.length === 1 && b[0] === 'ε') ? [prime] : b.concat([prime]));
      prods[Ai] = newAi.length ? newAi : [[prime]];
      for (const a of alphas) prods[prime].push((a.length === 1 && a[0] === 'ε') ? [prime] : a.concat([prime]));
      prods[prime].push(['ε']); nonterminals.push(prime);
    }
  }
  return prods;
}

/* ---------- Left factoring ---------- */
function leftFactorOnce(originalProds) {
  const prods = {}; for (const k of Object.keys(originalProds)) prods[k] = originalProds[k].map(r => r.slice());
  let changed = false;
  for (const A of Object.keys(prods)) {
    const rhss = prods[A]; if (rhss.length < 2) continue;
    const groups = {};
    for (const rhs of rhss) { const key = rhs[0] || 'ε'; (groups[key] = groups[key] || []).push(rhs); }
    for (const key of Object.keys(groups)) {
      const g = groups[key]; if (g.length <= 1) continue;
      let prefix = g[0].slice();
      for (let i = 1; i < g.length; i++) {
        const other = g[i]; let k = 0;
        while (k < prefix.length && k < other.length && prefix[k] === other[k]) k++;
        prefix = prefix.slice(0, k);
      }
      if (prefix.length === 0) continue;
      changed = true;
      let prime = A + "_fact"; while (prods[prime]) prime += "_";
      const newA = []; const factRHS = [];
      for (const rhs of rhss) {
        let matches = rhs.length >= prefix.length;
        for (let i = 0; i < prefix.length && matches; i++) if (rhs[i] !== prefix[i]) matches = false;
        if (matches) factRHS.push(rhs.slice(prefix.length).length ? rhs.slice(prefix.length) : ['ε']); else newA.push(rhs);
      }
      newA.push(prefix.concat([prime])); prods[A] = newA; prods[prime] = factRHS.map(r => r.slice());
      break;
    }
  }
  return { prods, changed };
}
function leftFactor(prods0) {
  let result = {}; for (const k of Object.keys(prods0)) result[k] = prods0[k].map(r => r.slice());
  for (let iter = 0; iter < 10; iter++) { const { prods, changed } = leftFactorOnce(result); result = prods; if (!changed) break; }
  return result;
}

/* ---------- LL(1) helpers ---------- */
function computeFirstOfString(rhs, FIRST, prods) {
  const res = new Set(); let nullablePrefix = true;
  for (const sym of rhs) {
    if (sym === 'ε') { res.add('ε'); nullablePrefix = true; break; }
    if (!prods[sym]) { res.add(sym); nullablePrefix = false; break; }
    for (const t of FIRST[sym]) if (t !== 'ε') res.add(t);
    if (!FIRST[sym].includes('ε')) { nullablePrefix = false; break; }
  }
  if (nullablePrefix) res.add('ε'); return res;
}
function buildPredictiveTable(prods, FIRST, FOLLOW) {
  const table = {}; for (const A of Object.keys(prods)) table[A] = {};
  const conflicts = [];
  for (const [A, rhss] of Object.entries(prods)) {
    for (const rhs of rhss) {
      const firstRhs = computeFirstOfString(rhs, FIRST, prods);
      for (const t of firstRhs) { if (t !== 'ε') { table[A][t] = table[A][t] || []; table[A][t].push(rhs); } }
      if (firstRhs.has('ε')) for (const b of (FOLLOW[A] || [])) { table[A][b] = table[A][b] || []; table[A][b].push(rhs); }
    }
  }
  for (const A of Object.keys(table)) for (const t of Object.keys(table[A])) if (table[A][t].length > 1) conflicts.push({ nonterminal: A, terminal: t, prods: table[A][t] });
  return { table, conflicts };
}
function tableToHTML(table) {
  const terms = new Set();
  for (const A of Object.keys(table)) for (const t of Object.keys(table[A] || {})) terms.add(t);
  const termArr = Array.from(terms).sort();
  let html = '<div style="overflow:auto"><table class="sets"><thead><tr><th>NT \\ t</th>';
  for (const t of termArr) html += `<th>${t}</th>`; html += '</tr></thead><tbody>';
  for (const A of Object.keys(table)) {
    html += `<tr><td><strong>${A}</strong></td>`;
    for (const t of termArr) {
      const cell = (table[A][t] || []).map(r => r.join(' ')).join(' || ');
      html += `<td style="min-width:120px">${cell || ''}</td>`;
    }
    html += '</tr>';
  }
  html += '</tbody></table></div>'; return html;
}

/* ---------- tab handling & lazy init ---------- */
const tabButtons = Array.from(document.querySelectorAll('.tab'));
const initialized = { first: false, leftrec: false, leftfact: false, ll1: false, regex: false };

// open FIRST panel by default
document.addEventListener('DOMContentLoaded', () => {
  const firstBtn = document.querySelector('.tab[data-tab="first"]');
  if (firstBtn) firstBtn.click();
});

// tab click: show only the selected panel, lazy-init its handlers
tabButtons.forEach(btn => {
  btn.addEventListener('click', () => {
    tabButtons.forEach(b => b.classList.remove('active'));
    btn.classList.add('active');
    const id = btn.dataset.tab;
    document.querySelectorAll('.tab-panel').forEach(p => p.classList.remove('active'));
    const panel = document.getElementById(id + '-panel');
    if (panel) panel.classList.add('active');

    // focus first field
    const focusable = panel.querySelector('textarea, input, button');
    if (focusable) focusable.focus({ preventScroll: true });

    // lazy init
    if (id === 'first' && !initialized.first) { initFirst(); initialized.first = true; }
    if (id === 'left-rec' && !initialized.leftrec) { initLeftRec(); initialized.leftrec = true; }
    if (id === 'left-fact' && !initialized.leftfact) { initLeftFact(); initialized.leftfact = true; }
    if (id === 'll1' && !initialized.ll1) { initLL1(); initialized.ll1 = true; }
    if (id === 'regex' && !initialized.regex) { initRegex(); initialized.regex = true; }

    // scroll card into view
    document.querySelector('.tool-card')?.scrollIntoView({ behavior: 'smooth', block: 'start' });
  });
});

/* ---------- per-tool initializers ---------- */

function initFirst() {
  const example = `E -> E + T | T
T -> T * F | F
F -> ( E ) | id`;
  const gramEl = document.getElementById('grammar-first');
  const resEl = document.getElementById('results-first');
  if (gramEl.value.trim() === '') gramEl.value = example;

  document.getElementById('example-first').addEventListener('click', () => { gramEl.value = example; toast('Example loaded'); });
  document.getElementById('copy-first-input').addEventListener('click', () => copyToClipboard(gramEl.value));
  document.getElementById('download-first-input').addEventListener('click', () => downloadText('grammar-first.txt', gramEl.value));
  document.getElementById('save-first').addEventListener('click', () => {
    const raw = gramEl.value.trim(); if (!raw) { toast('Nothing to save'); return; }
    localStorage.setItem('ctk_saved_first', raw); toast('Saved locally');
  });
  document.getElementById('load-first').addEventListener('click', () => {
    const s = localStorage.getItem('ctk_saved_first'); if (!s) { toast('No saved grammar'); return; }
    gramEl.value = s; toast('Loaded saved grammar');
  });

  document.getElementById('compute-first').addEventListener('click', () => {
    const raw = gramEl.value.trim(); if (!raw) { toast('Enter grammar'); return; }
    const prods = parseGrammar(raw); if (!Object.keys(prods).length) { toast('Parse failed'); return; }
    const start = Object.keys(prods)[0]; const FIRST = computeFirst(prods); const FOLLOW = computeFollow(prods, FIRST, start);
    resEl.innerHTML = `<div style="display:flex;gap:18px;flex-wrap:wrap"><div style="min-width:260px">${prettySetsHTML(FIRST)}</div><div style="min-width:260px">${prettySetsHTML(FOLLOW)}</div></div>`;
    toast('FIRST & FOLLOW computed');
  });

  document.getElementById('copy-first-output').addEventListener('click', () => copyToClipboard(resEl.innerText || ''));
  document.getElementById('download-first-output').addEventListener('click', () => downloadText('first-follow-results.txt', resEl.innerText || ''));
}

function initLeftRec() {
  const example = `S -> S a | b`;
  const inEl = document.getElementById('grammar-leftrec');
  const outEl = document.getElementById('leftrec-output');
  if (inEl.value.trim() === '') inEl.value = example;

  document.getElementById('example-leftrec').addEventListener('click', () => { inEl.value = example; toast('Example loaded'); });
  document.getElementById('copy-leftrec-input').addEventListener('click', () => copyToClipboard(inEl.value));
  document.getElementById('run-leftrec').addEventListener('click', () => {
    const raw = inEl.value.trim(); if (!raw) { toast('Enter grammar'); return; }
    const prods = parseGrammar(raw); const transformed = eliminateLeftRecursion(prods);
    outEl.textContent = 'Original:\n' + stringifyGrammar(prods) + '\n\nTransformed:\n' + stringifyGrammar(transformed);
    toast('Left recursion removed (where present)');
  });

  document.getElementById('copy-leftrec-output').addEventListener('click', () => copyToClipboard(outEl.textContent || ''));
  document.getElementById('download-leftrec-output').addEventListener('click', () => downloadText('leftrec-result.txt', outEl.textContent || ''));
  document.getElementById('use-leftrec-in-first').addEventListener('click', () => {
    const txt = outEl.textContent || ''; if (!txt) { toast('No output to use'); return; }
    const idx = txt.indexOf('Transformed:'); if (idx === -1) { toast('No transformed block'); return; }
    const transformed = txt.slice(idx + 'Transformed:'.length).trim();
    const firstGram = document.getElementById('grammar-first'); if (firstGram) { firstGram.value = transformed; toast('Placed in FIRST tab'); }
  });
}

function initLeftFact() {
  const example = `A -> a b c | a b d | a x | b y`;
  const inEl = document.getElementById('grammar-leftfact');
  const outEl = document.getElementById('leftfact-output');
  if (inEl.value.trim() === '') inEl.value = example;

  document.getElementById('example-leftfact').addEventListener('click', () => { inEl.value = example; toast('Example loaded'); });
  document.getElementById('copy-leftfact-input').addEventListener('click', () => copyToClipboard(inEl.value));
  document.getElementById('run-leftfact').addEventListener('click', () => {
    const raw = inEl.value.trim(); if (!raw) { toast('Enter grammar'); return; }
    const prods = parseGrammar(raw); const transformed = leftFactor(prods);
    outEl.textContent = 'Original:\n' + stringifyGrammar(prods) + '\n\nFactored:\n' + stringifyGrammar(transformed);
    toast('Left factoring applied');
  });

  document.getElementById('copy-leftfact-output').addEventListener('click', () => copyToClipboard(outEl.textContent || ''));
  document.getElementById('download-leftfact-output').addEventListener('click', () => downloadText('leftfact-result.txt', outEl.textContent || ''));
  document.getElementById('use-leftfact-in-first').addEventListener('click', () => {
    const txt = outEl.textContent || ''; if (!txt) { toast('No output'); return; }
    const idx = txt.indexOf('Factored:'); if (idx === -1) { toast('No factored block'); return; }
    const transformed = txt.slice(idx + 'Factored:'.length).trim();
    const firstGram = document.getElementById('grammar-first'); if (firstGram) { firstGram.value = transformed; toast('Placed in FIRST tab'); }
  });
}

function initLL1() {
  const example = `E -> T E'\nE' -> + T E' | ε\nT -> F T'\nT' -> * F T' | ε\nF -> ( E ) | id`;
  const inEl = document.getElementById('grammar-ll1');
  const outEl = document.getElementById('ll1-output');
  if (inEl.value.trim() === '') inEl.value = example;

  document.getElementById('example-ll1').addEventListener('click', () => { inEl.value = example; toast('Example loaded'); });
  document.getElementById('copy-ll1-input').addEventListener('click', () => copyToClipboard(inEl.value));
  document.getElementById('run-ll1').addEventListener('click', () => {
    const raw = inEl.value.trim(); if (!raw) { toast('Enter grammar'); return; }
    const prods = parseGrammar(raw);
    if (!Object.keys(prods).length) { toast('Parse failed'); return; }
    const start = Object.keys(prods)[0]; const FIRST = computeFirst(prods); const FOLLOW = computeFollow(prods, FIRST, start);
    const { table, conflicts } = buildPredictiveTable(prods, FIRST, FOLLOW);
    let html = `<div><strong>FIRST</strong>${prettySetsHTML(FIRST)}</div><div style="margin-top:8px"><strong>FOLLOW</strong>${prettySetsHTML(FOLLOW)}</div>`;
    html += `<div style="margin-top:8px"><strong>Predictive table</strong>${tableToHTML(table)}</div>`;
    html += `<div style="margin-top:8px"><strong>Conflicts</strong><pre>${conflicts.length === 0 ? 'No conflicts — grammar appears LL(1)' : conflicts.map(c=>'NT '+c.nonterminal+' on '+c.terminal+': '+c.prods.map(r=>r.join(' ')).join(' || ')).join('\n')}</pre></div>`;
    outEl.innerHTML = html;
    toast('LL(1) analysis complete');
  });

  document.getElementById('copy-ll1-output').addEventListener('click', () => copyToClipboard(outEl.innerText || ''));
  document.getElementById('download-ll1-output').addEventListener('click', () => downloadText('ll1-output.txt', outEl.innerText || ''));

  document.getElementById('auto-pipeline').addEventListener('click', () => {
    const raw = inEl.value.trim(); if (!raw) { toast('Enter grammar'); return; }
    let prods = parseGrammar(raw);
    prods = eliminateLeftRecursion(prods);
    prods = leftFactor(prods);
    const transformed = stringifyGrammar(prods);
    inEl.value = transformed;
    document.getElementById('leftrec-output').textContent = transformed;
    document.getElementById('leftfact-output').textContent = transformed;
    toast('Pipeline applied — transformed grammar placed in LL(1) input');
  });
}

function initRegex() {
  const patEl = document.getElementById('regex-pattern');
  const flagsEl = document.getElementById('regex-flags');
  const textEl = document.getElementById('regex-text');
  const outEl = document.getElementById('regex-output');

  if (!patEl.value.trim() && !textEl.value.trim()) {
    patEl.value = '\\b\\d+\\b'; flagsEl.value = 'g'; textEl.value = 'Order numbers: 42, 256, and 1024.';
  }

  document.getElementById('example-regex').addEventListener('click', () => {
    patEl.value = '\\b\\d+\\b'; flagsEl.value = 'g'; textEl.value = 'Order numbers: 42, 256, and 1024.'; toast('Example loaded');
  });

  document.getElementById('copy-regex-input').addEventListener('click', () => copyToClipboard(patEl.value + ' / ' + flagsEl.value + '\n\n' + textEl.value));
  document.getElementById('run-regex').addEventListener('click', () => {
    const pattern = patEl.value; const flags = flagsEl.value || ''; const text = textEl.value || '';
    try {
      const re = new RegExp(pattern, flags);
      const matches = Array.from(text.matchAll(re)).map(m => ({ match: m[0], index: m.index, groups: m.slice(1) }));
      outEl.textContent = JSON.stringify({ matches }, null, 2);
      toast('Regex tested');
    } catch (e) {
      outEl.textContent = 'Error: ' + e.message; toast('Invalid regex');
    }
  });
  document.getElementById('copy-regex-output').addEventListener('click', () => copyToClipboard(outEl.textContent || ''));
  document.getElementById('download-regex-output').addEventListener('click', () => downloadText('regex-results.txt', outEl.textContent || ''));
}
/* js/tools.js - single-panel layout with left inputs and right outputs.
   Tools included: FIRST/FOLLOW, Left Recursion elimination, Left Factoring,
   LL(1) predictive table, Regex tester. Panels are lazy-initialized.
*/

/* --- helpers --- */
function toast(msg, t = 1600) {
  let c = document.getElementById('__toast_container');
  if (!c) { c = document.createElement('div'); c.id='__toast_container'; c.style.position='fixed'; c.style.right='18px'; c.style.bottom='18px'; c.style.zIndex=9999; document.body.appendChild(c); }
  const el = document.createElement('div'); el.textContent = msg;
  Object.assign(el.style,{background:'#111',color:'#fff',padding:'8px 12px',marginTop:'8px',borderRadius:'8px',fontSize:'13px'});
  c.appendChild(el); setTimeout(()=>{ el.style.transition='all .28s'; el.style.opacity='0'; el.style.transform='translateX(30px)'; setTimeout(()=>el.remove(),280); }, t);
}
function downloadText(name,text){ const a=document.createElement('a'); a.href=URL.createObjectURL(new Blob([text],{type:'text/plain'})); a.download=name; document.body.appendChild(a); a.click(); a.remove(); }
function copyToClipboard(text){ navigator.clipboard?.writeText(text).then(()=>toast('Copied'), ()=>toast('Copy failed')); }

/* --- grammar parse/stringify --- */
function parseGrammar(text){
  const lines = text.split('\n').map(s=>s.trim()).filter(Boolean);
  const prods = {};
  for(const line of lines){
    const idx = line.indexOf('->'); if(idx === -1) continue;
    const lhs = line.slice(0, idx).trim();
    const rhsText = line.slice(idx+2).trim();
    const alts = rhsText.split('|').map(x=>x.trim()).filter(Boolean);
    if(!prods[lhs]) prods[lhs] = [];
    for(const alt of alts){
      const toks = alt === '' ? ['ε'] : alt.split(/\s+/).map(t => t==='epsilon' ? 'ε' : t);
      prods[lhs].push(toks.length ? toks : ['ε']);
    }
  }
  return prods;
}
function stringifyGrammar(prods){
  return Object.keys(prods).map(k => `${k} -> ${prods[k].map(r=>r.join(' ')).join(' | ')}`).join('\n');
}

/* --- FIRST / FOLLOW algorithms --- */
function computeFirst(prods){
  const FIRST = {}; for(const A of Object.keys(prods)) FIRST[A] = new Set();
  let changed = true;
  while(changed){
    changed = false;
    for(const [A,rhss] of Object.entries(prods)){
      for(const rhs of rhss){
        let nullable = true;
        for(const sym of rhs){
          if(sym === 'ε'){ if(!FIRST[A].has('ε')){ FIRST[A].add('ε'); changed=true;} nullable=false; break; }
          if(!prods[sym]){ if(!FIRST[A].has(sym)){ FIRST[A].add(sym); changed=true;} nullable=false; break; }
          for(const t of FIRST[sym]) if(t!=='ε' && !FIRST[A].has(t)){ FIRST[A].add(t); changed=true; }
          if(!FIRST[sym].has('ε')){ nullable=false; break; }
        }
        if(nullable){ if(!FIRST[A].has('ε')){ FIRST[A].add('ε'); changed=true; } }
      }
    }
  }
  const out = {}; for(const [k,s] of Object.entries(FIRST)) out[k]=Array.from(s);
  return out;
}
function computeFollow(prods,FIRST,start){
  const follow = {}; for(const A of Object.keys(prods)) follow[A] = new Set();
  follow[start].add('$');
  let changed = true;
  while(changed){
    changed=false;
    for(const [A,rhss] of Object.entries(prods)){
      for(const rhs of rhss){
        for(let i=0;i<rhs.length;i++){
          const B = rhs[i]; if(!prods[B]) continue;
          let firstBeta = new Set(); let betaNullable = true;
          for(let j=i+1;j<rhs.length;j++){
            const s = rhs[j];
            if(s==='ε'){ firstBeta.add('ε'); betaNullable=true; break; }
            if(!prods[s]){ firstBeta.add(s); betaNullable=false; break; }
            for(const t of FIRST[s]) if(t!=='ε') firstBeta.add(t);
            if(!FIRST[s].includes('ε')){ betaNullable=false; break; }
          }
          if(i === rhs.length-1) betaNullable = true;
          for(const t of firstBeta) if(t!=='ε' && !follow[B].has(t)){ follow[B].add(t); changed=true; }
          if(betaNullable) for(const t of follow[A]) if(!follow[B].has(t)){ follow[B].add(t); changed=true; }
        }
      }
    }
  }
  const out = {}; for(const [k,s] of Object.entries(follow)) out[k]=Array.from(s);
  return out;
}
function prettySetsHTML(obj){
  if(!obj) return '<div>—</div>';
  let html = '<table class="sets"><thead><tr><th>Symbol</th><th>Set</th></tr></thead><tbody>';
  const keys = Object.keys(obj).sort();
  for(const k of keys) html += `<tr><td><strong>${k}</strong></td><td>${(obj[k]||[]).join(', ') || '—'}</td></tr>`;
  html += '</tbody></table>'; return html;
}

/* --- left recursion elimination --- */
function eliminateLeftRecursion(originalProds){
  const prods = {}; for(const k of Object.keys(originalProds)) prods[k]=originalProds[k].map(r=>r.slice());
  const nonterminals = Object.keys(prods);
  for(let i=0;i<nonterminals.length;i++){
    const Ai = nonterminals[i];
    for(let j=0;j<i;j++){
      const Aj = nonterminals[j];
      const newRHS = [];
      for(const rhs of prods[Ai]){
        if(rhs[0] === Aj){
          for(const delta of prods[Aj]){
            const combined = (delta.length===1 && delta[0]==='ε') ? rhs.slice(1) : delta.concat(rhs.slice(1));
            newRHS.push(combined.length ? combined : ['ε']);
          }
        } else newRHS.push(rhs);
      }
      prods[Ai] = newRHS;
    }
    const alphas = [], betas = [];
    for(const rhs of prods[Ai]){
      if(rhs[0] === Ai){ const rest = rhs.slice(1); alphas.push(rest.length?rest:['ε']); }
      else betas.push(rhs);
    }
    if(alphas.length > 0){
      let prime = Ai + "'"; while(prods[prime]) prime += "'";
      prods[prime] = [];
      const newAi = [];
      for(const b of betas) newAi.push((b.length===1 && b[0]==='ε') ? [prime] : b.concat([prime]));
      prods[Ai] = newAi.length ? newAi : [[prime]];
      for(const a of alphas) prods[prime].push((a.length===1 && a[0]==='ε') ? [prime] : a.concat([prime]));
      prods[prime].push(['ε']); nonterminals.push(prime);
    }
  }
  return prods;
}

/* --- left factoring --- */
function leftFactorOnce(originalProds){
  const prods = {}; for(const k of Object.keys(originalProds)) prods[k]=originalProds[k].map(r=>r.slice());
  let changed=false;
  for(const A of Object.keys(prods)){
    const rhss = prods[A]; if(rhss.length<2) continue;
    const groups = {};
    for(const rhs of rhss){ const key = rhs[0] || 'ε'; (groups[key]=groups[key]||[]).push(rhs); }
    for(const key of Object.keys(groups)){
      const g = groups[key]; if(g.length<=1) continue;
      let prefix = g[0].slice();
      for(let i=1;i<g.length;i++){ const other=g[i]; let k=0; while(k<prefix.length && k<other.length && prefix[k]===other[k]) k++; prefix = prefix.slice(0,k); }
      if(prefix.length===0) continue;
      changed=true;
      let prime = A + "_fact"; while(prods[prime]) prime += "_";
      const newA = [], factRHS = [];
      for(const rhs of rhss){
        let matches = rhs.length >= prefix.length;
        for(let i=0;i<prefix.length && matches;i++) if(rhs[i] !== prefix[i]) matches=false;
        if(matches) factRHS.push(rhs.slice(prefix.length).length ? rhs.slice(prefix.length) : ['ε']); else newA.push(rhs);
      }
      newA.push(prefix.concat([prime])); prods[A] = newA; prods[prime] = factRHS.map(r=>r.slice()); break;
    }
  }
  return {prods, changed};
}
function leftFactor(prods0){
  let result = {}; for(const k of Object.keys(prods0)) result[k] = prods0[k].map(r=>r.slice());
  for(let iter=0; iter<10; iter++){ const {prods, changed} = leftFactorOnce(result); result = prods; if(!changed) break; }
  return result;
}

/* --- LL(1) helpers --- */
function computeFirstOfString(rhs,FIRST,prods){
  const res = new Set(); let nullable = true;
  for(const sym of rhs){
    if(sym==='ε'){ res.add('ε'); nullable=true; break; }
    if(!prods[sym]){ res.add(sym); nullable=false; break; }
    for(const t of FIRST[sym]) if(t!=='ε') res.add(t);
    if(!FIRST[sym].includes('ε')){ nullable=false; break; }
  }
  if(nullable) res.add('ε'); return res;
}
function buildPredictiveTable(prods,FIRST,FOLLOW){
  const table={}; for(const A of Object.keys(prods)) table[A]={};
  const conflicts=[];
  for(const [A,rhss] of Object.entries(prods)){
    for(const rhs of rhss){
      const firstRhs = computeFirstOfString(rhs,FIRST,prods);
      for(const t of firstRhs) if(t!=='ε'){ table[A][t] = table[A][t]||[]; table[A][t].push(rhs); }
      if(firstRhs.has('ε')) for(const b of (FOLLOW[A]||[])){ table[A][b] = table[A][b]||[]; table[A][b].push(rhs); }
    }
  }
  for(const A of Object.keys(table)) for(const t of Object.keys(table[A])) if(table[A][t].length>1) conflicts.push({nonterminal:A, terminal:t, prods:table[A][t]});
  return {table,conflicts};
}
function tableToHTML(table){
  const terms = new Set();
  for(const A of Object.keys(table)) for(const t of Object.keys(table[A]||{})) terms.add(t);
  const termArr = Array.from(terms).sort();
  let html = '<div style="overflow:auto"><table class="sets"><thead><tr><th>NT \\ t</th>';
  for(const t of termArr) html += `<th>${t}</th>`; html += '</tr></thead><tbody>';
  for(const A of Object.keys(table)){ html += `<tr><td><strong>${A}</strong></td>`; for(const t of termArr){ const cell = (table[A][t]||[]).map(r=>r.join(' ')).join(' || '); html += `<td style="min-width:120px">${cell||''}</td>` } html += '</tr>'; }
  html += '</tbody></table></div>'; return html;
}

/* --- tab & lazy init --- */
const tabs = Array.from(document.querySelectorAll('.tab'));
const initialized = { first:false, leftrec:false, leftfact:false, ll1:false, regex:false };

function showPanel(id){
  document.querySelectorAll('.tab').forEach(b=>b.classList.remove('active'));
  document.querySelector(`.tab[data-tab="${id}"]`)?.classList.add('active');
  document.querySelectorAll('.tab-panel').forEach(p=>p.classList.remove('active'));
  const panel = document.getElementById(id + '-panel'); panel?.classList.add('active');
  panel?.querySelector('textarea, input, button')?.focus({preventScroll:true});
  // lazy init
  if(id==='first' && !initialized.first){ initFirst(); initialized.first=true; }
  if(id==='left-rec' && !initialized.leftrec){ initLeftRec(); initialized.leftrec=true; }
  if(id==='left-fact' && !initialized.leftfact){ initLeftFact(); initialized.leftfact=true; }
  if(id==='ll1' && !initialized.ll1){ initLL1(); initialized.ll1=true; }
  if(id==='regex' && !initialized.regex){ initRegex(); initialized.regex=true; }
}

tabs.forEach(btn => btn.addEventListener('click', ()=> showPanel(btn.dataset.tab)));

// open FIRST by default
document.addEventListener('DOMContentLoaded', ()=> showPanel('first'));

/* --- per-tool initializers --- */

function initFirst(){
  const example = `E -> E + T | T
T -> T * F | F
F -> ( E ) | id`;
  const gram = document.getElementById('grammar-first');
  const firstOut = document.getElementById('first-output');
  const followOut = document.getElementById('follow-output');
  if(gram.value.trim()==='') gram.value = example;

  document.getElementById('example-first').addEventListener('click', ()=> { gram.value = example; toast('Example loaded'); });
  document.getElementById('copy-first-input').addEventListener('click', ()=> copyToClipboard(gram.value));
  document.getElementById('download-first-input').addEventListener('click', ()=> downloadText('grammar-first.txt', gram.value));

  document.getElementById('compute-first').addEventListener('click', ()=>{
    const raw = gram.value.trim(); if(!raw){ toast('Enter grammar'); return; }
    const prods = parseGrammar(raw); if(!Object.keys(prods).length){ toast('Parse failed'); return; }
    const start = Object.keys(prods)[0];
    const FIRST = computeFirst(prods);
    const FOLLOW = computeFollow(prods, FIRST, start);
    firstOut.innerHTML = prettySetsHTML(FIRST);
    followOut.innerHTML = prettySetsHTML(FOLLOW);
    toast('Computed FIRST & FOLLOW');
  });

  document.getElementById('copy-first-output').addEventListener('click', ()=> copyToClipboard(firstOut.innerText + '\n\n' + followOut.innerText));
  document.getElementById('download-first-output').addEventListener('click', ()=> downloadText('first-follow-results.txt', firstOut.innerText + '\n\n' + followOut.innerText));
}

function initLeftRec(){
  const example = `S -> S a | b`;
  const gram = document.getElementById('grammar-leftrec');
  const out = document.getElementById('leftrec-output');
  if(gram.value.trim()==='') gram.value = example;

  document.getElementById('example-leftrec').addEventListener('click', ()=> { gram.value = example; toast('Example loaded'); });
  document.getElementById('copy-leftrec-input').addEventListener('click', ()=> copyToClipboard(gram.value));
  document.getElementById('run-leftrec').addEventListener('click', ()=>{
    const raw = gram.value.trim(); if(!raw){ toast('Enter grammar'); return; }
    const prods = parseGrammar(raw); const transformed = eliminateLeftRecursion(prods);
    out.textContent = 'Original:\n' + stringifyGrammar(prods) + '\n\nTransformed:\n' + stringifyGrammar(transformed);
    toast('Left recursion transformed');
  });

  document.getElementById('copy-leftrec-output').addEventListener('click', ()=> copyToClipboard(out.textContent || ''));
  document.getElementById('download-leftrec-output').addEventListener('click', ()=> downloadText('leftrec-result.txt', out.textContent || ''));
  document.getElementById('use-leftrec-in-first').addEventListener('click', ()=>{
    const txt = out.textContent || ''; if(!txt){ toast('No output'); return; }
    const idx = txt.indexOf('Transformed:'); if(idx === -1){ toast('No transformed block'); return; }
    const transformed = txt.slice(idx + 'Transformed:'.length).trim();
    document.getElementById('grammar-first').value = transformed; toast('Placed in FIRST tab');
  });
}

function initLeftFact(){
  const example = `A -> a b c | a b d | a x | b y`;
  const gram = document.getElementById('grammar-leftfact');
  const out = document.getElementById('leftfact-output');
  if(gram.value.trim()==='') gram.value = example;

  document.getElementById('example-leftfact').addEventListener('click', ()=> { gram.value = example; toast('Example loaded'); });
  document.getElementById('copy-leftfact-input').addEventListener('click', ()=> copyToClipboard(gram.value));
  document.getElementById('run-leftfact').addEventListener('click', ()=>{
    const raw = gram.value.trim(); if(!raw){ toast('Enter grammar'); return; }
    const prods = parseGrammar(raw); const transformed = leftFactor(prods);
    out.textContent = 'Original:\n' + stringifyGrammar(prods) + '\n\nFactored:\n' + stringifyGrammar(transformed);
    toast('Left factoring applied');
  });

  document.getElementById('copy-leftfact-output').addEventListener('click', ()=> copyToClipboard(out.textContent || ''));
  document.getElementById('download-leftfact-output').addEventListener('click', ()=> downloadText('leftfact-result.txt', out.textContent || ''));
  document.getElementById('use-leftfact-in-first').addEventListener('click', ()=>{
    const txt = out.textContent || ''; if(!txt){ toast('No output'); return; }
    const idx = txt.indexOf('Factored:'); if(idx === -1){ toast('No factored block'); return; }
    const transformed = txt.slice(idx + 'Factored:'.length).trim();
    document.getElementById('grammar-first').value = transformed; toast('Placed in FIRST tab');
  });
}

function initLL1(){
  const example = `E -> T E'\nE' -> + T E' | ε\nT -> F T'\nT' -> * F T' | ε\nF -> ( E ) | id`;
  const gram = document.getElementById('grammar-ll1');
  const out = document.getElementById('ll1-output');
  if(gram.value.trim()==='') gram.value = example;

  document.getElementById('example-ll1').addEventListener('click', ()=> { gram.value = example; toast('Example loaded'); });
  document.getElementById('run-ll1').addEventListener('click', ()=>{
    const raw = gram.value.trim(); if(!raw){ toast('Enter grammar'); return; }
    const prods = parseGrammar(raw); if(!Object.keys(prods).length){ toast('Parse failed'); return; }
    const start = Object.keys(prods)[0]; const FIRST = computeFirst(prods); const FOLLOW = computeFollow(prods,FIRST,start);
    const {table, conflicts} = buildPredictiveTable(prods,FIRST,FOLLOW);
    let html = `<div><strong>FIRST</strong>${prettySetsHTML(FIRST)}</div><div style="margin-top:8px"><strong>FOLLOW</strong>${prettySetsHTML(FOLLOW)}</div>`;
    html += `<div style="margin-top:8px"><strong>Predictive table</strong>${tableToHTML(table)}</div>`;
    html += `<div style="margin-top:8px"><strong>Conflicts</strong><pre>${conflicts.length === 0 ? 'No conflicts — grammar appears LL(1)' : conflicts.map(c=>'NT '+c.nonterminal+' on '+c.terminal+': '+c.prods.map(r=>r.join(' ')).join(' || ')).join('\n')}</pre></div>`;
    out.innerHTML = html; toast('LL(1) analysis complete');
  });

  document.getElementById('copy-ll1-output').addEventListener('click', ()=> copyToClipboard(out.innerText || ''));
  document.getElementById('download-ll1-output').addEventListener('click', ()=> downloadText('ll1-output.txt', out.innerText || ''));

  document.getElementById('auto-pipeline').addEventListener('click', ()=>{
    const raw = gram.value.trim(); if(!raw){ toast('Enter grammar'); return; }
    let prods = parseGrammar(raw); prods = eliminateLeftRecursion(prods); prods = leftFactor(prods);
    const transformed = stringifyGrammar(prods); gram.value = transformed;
    document.getElementById('leftrec-output').textContent = transformed; document.getElementById('leftfact-output').textContent = transformed;
    toast('Pipeline applied (left recursion removed + factoring)');
  });
}

function initRegex(){
  const pat = document.getElementById('regex-pattern');
  const text = document.getElementById('regex-text');
  const highlight = document.getElementById('regex-highlight');
  const list = document.getElementById('regex-list');

  if(!pat.value.trim() && !text.value.trim()){
    pat.value = 'a(b|c)+';
    text.value = 'test abc abb acbc aXc';
  }

  document.getElementById('example-regex').addEventListener('click', ()=> { pat.value='a(b|c)+'; text.value='test abc abb acbc aXc'; toast('Example loaded'); });
  document.getElementById('copy-regex-input').addEventListener('click', ()=> copyToClipboard(pat.value + '\n\n' + text.value));
  document.getElementById('run-regex').addEventListener('click', ()=>{
    const pattern = pat.value; const sample = text.value || '';
    if(!pattern){ toast('Enter pattern'); return; }
    try{
      const re = new RegExp(pattern,'g'); // global so we can find all
      const matches = Array.from(sample.matchAll(re)).map(m => ({ text: m[0], index: m.index, groups: m.slice(1) }));
      // highlight sample text
      let last = 0; let outHtml = '';
      for(const m of matches){
        outHtml += escapeHtml(sample.slice(last, m.index)) + `<span class="match">${escapeHtml(m.text)}</span>`;
        last = m.index + m.text.length;
      }
      outHtml += escapeHtml(sample.slice(last));
      highlight.innerHTML = outHtml || '<div class="muted">No matches</div>';
      // match list
      if(matches.length === 0) list.innerHTML = '<div class="muted">No matches</div>';
      else list.innerHTML = matches.map(m => `<div style="display:flex;justify-content:space-between;padding:8px;border-radius:8px;background:#fbfbfb;margin-bottom:6px"><div>${escapeHtml(m.text)}</div><div style="color:var(--muted)">[${m.index}, ${m.index + m.text.length - 1}]</div></div>`).join('');
      toast('Regex tested (' + matches.length + ' match' + (matches.length!==1?'es':'') + ')');
    }catch(e){
      highlight.textContent = 'Error: ' + e.message; list.textContent = ''; toast('Invalid regex');
    }
  });

  document.getElementById('copy-regex-output').addEventListener('click', ()=> copyToClipboard(highlight.innerText + '\n\n' + list.innerText));
  document.getElementById('download-regex-output').addEventListener('click', ()=> downloadText('regex-results.txt', highlight.innerText + '\n\n' + list.innerText));
}

/* helper: escape HTML for safe display */
function escapeHtml(s){ return (s+'').replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;'); }

/* buildPredictiveTable used in LL1 initializer */
function computeFirstOfString(rhs,FIRST,prods){
  const res = new Set(); let nullable=true;
  for(const sym of rhs){
    if(sym==='ε'){ res.add('ε'); nullable=true; break; }
    if(!prods[sym]){ res.add(sym); nullable=false; break; }
    for(const t of FIRST[sym]) if(t!=='ε') res.add(t);
    if(!FIRST[sym].includes('ε')){ nullable=false; break; }
  }
  if(nullable) res.add('ε'); return res;
}
function buildPredictiveTable(prods,FIRST,FOLLOW){
  const table={}; for(const A of Object.keys(prods)) table[A]={};
  const conflicts=[];
  for(const [A,rhss] of Object.entries(prods)){
    for(const rhs of rhss){
      const firstRhs = computeFirstOfString(rhs,FIRST,prods);
      for(const t of firstRhs) if(t!=='ε'){ table[A][t] = table[A][t]||[]; table[A][t].push(rhs); }
      if(firstRhs.has('ε')) for(const b of (FOLLOW[A]||[])){ table[A][b] = table[A][b]||[]; table[A][b].push(rhs); }
    }
  }
  for(const A of Object.keys(table)) for(const t of Object.keys(table[A])) if(table[A][t].length>1) conflicts.push({nonterminal:A,terminal:t,prods:table[A][t]});
  return {table,conflicts};
}
function tableToHTML(table){
  const terms = new Set();
  for(const A of Object.keys(table)) for(const t of Object.keys(table[A]||{})) terms.add(t);
  const termArr = Array.from(terms).sort();
  let html = '<div style="overflow:auto"><table class="sets"><thead><tr><th>NT \\ t</th>';
  for(const t of termArr) html += `<th>${t}</th>`; html += '</tr></thead><tbody>';
  for(const A of Object.keys(table)){ html += `<tr><td><strong>${A}</strong></td>`; for(const t of termArr){ const cell = (table[A][t]||[]).map(r=>r.join(' ')).join(' || '); html += `<td style="min-width:120px">${cell||''}</td>` } html += '</tr>'; }
  html += '</tbody></table></div>'; return html;
}

/* Exported functions computeFirst / computeFollow used above */
function computeFirst(prods){ return (function inner(){ return (function(){})() })(); } // placeholder, real computeFirst is defined above earlier (redeclared)
/* Note: computeFirst declared earlier. No further actions. */

