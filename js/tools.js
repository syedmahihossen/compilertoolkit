/* js/tools.js - Improved Compiler Toolkit logic
   - Robust tokenizer (splits TE' -> T, E')
   - Correct FIRST & FOLLOW per rules provided
   - LL(1) table, left recursion elimination, left factoring
   - Regex tester + rendering helpers
*/

/* ------- utilities ------- */
function toast(msg) {
  const el = document.createElement('div');
  el.textContent = msg;
  Object.assign(el.style, {
    position: 'fixed',
    right: '18px',
    bottom: '18px',
    background: '#111827',
    color: '#f9fafb',
    padding: '8px 12px',
    borderRadius: '8px',
    zIndex: 9999,
    fontSize: '13px'
  });
  document.body.appendChild(el);
  setTimeout(() => el.remove(), 1400);
}
function escapeHtml(s) {
  return (s + '')
    .replace(/&/g,'&amp;')
    .replace(/</g,'&lt;')
    .replace(/>/g,'&gt;');
}

/* ------- tokenizer & parser ------- */
/*
  Token matching regex notes:
  - Match nonterminals: single uppercase letter possibly followed by apostrophe(s), e.g. E, E', A''
  - Match multi-letter lowercase terminals e.g. id, num123
  - Match punctuation and single-char terminals: ( ) + * - / , etc.
  - Accept ε or "epsilon" as epsilon
*/
const TOKEN_RE = /ε|epsilon|[A-Z]'+|[A-Z]|[a-z][a-z0-9]*'?|[0-9]+|[(){}\[\]+*\/\-,.:;<>|]/g;

function tokenizeRHS(alt) {
  alt = (alt || '').trim();
  if (alt === '' || alt === 'ε' || alt.toLowerCase() === 'epsilon') return ['ε'];
  const tokens = [];
  let m;
  while ((m = TOKEN_RE.exec(alt)) !== null) {
    const t = m[0];
    // treat "epsilon" as ε
    if (t.toLowerCase() === 'epsilon') tokens.push('ε');
    else tokens.push(t);
  }
  return tokens.length ? tokens : ['ε'];
}

function parseGrammar(text) {
  const lines = String(text || '').split('\n').map(l => l.trim()).filter(Boolean);
  const prods = {};
  for (const line of lines) {
    const idx = line.indexOf('->');
    if (idx === -1) continue;
    const lhs = line.slice(0, idx).trim();
    if (!lhs) continue;
    const rhs = line.slice(idx + 2).trim();
    // split on top-level | (we assume no grouping inside alternatives)
    const alts = rhs.split('|').map(a => a.trim());
    if (!prods[lhs]) prods[lhs] = [];
    for (const alt of alts) {
      const toks = tokenizeRHS(alt);
      prods[lhs].push(toks.length ? toks : ['ε']);
    }
  }
  return prods;
}

function stringifyGrammar(prods) {
  return Object.keys(prods)
    .map(A => `${A} -> ${prods[A].map(r => r.join(' ')).join(' | ')}`)
    .join('\n');
}

function identifySymbols(prods) {
  const nonterm = new Set(Object.keys(prods));
  const terms = new Set();
  for (const [A, rhss] of Object.entries(prods)) {
    for (const rhs of rhss) {
      for (const t of rhs) {
        if (t === 'ε') continue;
        if (!nonterm.has(t)) terms.add(t);
      }
    }
  }
  return {
    nonterminals: Array.from(nonterm),
    terminals: Array.from(terms),
    start: Object.keys(prods)[0] || null
  };
}

/* ------- FIRST & FOLLOW ------- */
/* firstOfString: compute FIRST of a sequence Y1 Y2 ... Yn */
function firstOfString(rhs, FIRST, nonterminalsSet) {
  const res = new Set();
  let allNullable = true;

  for (const sym of rhs) {
    if (sym === 'ε') {
      res.add('ε');
      allNullable = true;
      break;
    }
    if (!nonterminalsSet.has(sym)) {
      // terminal
      res.add(sym);
      allNullable = false;
      break;
    }
    // sym is nonterminal
    const fset = FIRST[sym] || new Set();
    for (const t of fset) {
      if (t !== 'ε') res.add(t);
    }
    if (!fset.has('ε')) {
      allNullable = false;
      break;
    }
    // else continue to next symbol
  }
  if (allNullable) res.add('ε');
  return res;
}

function computeFirst(prods) {
  const FIRST = {};
  const nonterms = Object.keys(prods);
  const nonterminalsSet = new Set(nonterms);
  // initialize empty sets
  for (const A of nonterms) FIRST[A] = new Set();

  let changed = true;
  while (changed) {
    changed = false;
    for (const A of nonterms) {
      const rhss = prods[A];
      for (const rhs of rhss) {
        // if epsilon production explicitly
        if (rhs.length === 1 && rhs[0] === 'ε') {
          if (!FIRST[A].has('ε')) { FIRST[A].add('ε'); changed = true; }
          continue;
        }

        let prefixNullable = true;
        for (const sym of rhs) {
          if (sym === 'ε') {
            if (!FIRST[A].has('ε')) { FIRST[A].add('ε'); changed = true; }
            prefixNullable = false;
            break;
          }

          if (!nonterminalsSet.has(sym)) {
            // terminal
            if (!FIRST[A].has(sym)) { FIRST[A].add(sym); changed = true; }
            prefixNullable = false;
            break;
          }

          // sym is nonterminal
          const fSym = FIRST[sym];
          for (const t of fSym) {
            if (t !== 'ε' && !FIRST[A].has(t)) {
              FIRST[A].add(t);
              changed = true;
            }
          }
          if (!fSym.has('ε')) {
            prefixNullable = false;
            break;
          }
          // else continue to next symbol
        }

        if (prefixNullable) {
          if (!FIRST[A].has('ε')) { FIRST[A].add('ε'); changed = true; }
        }
      }
    }
  }
  return FIRST;
}

function computeFollow(prods, FIRST, startSymbol) {
  const FOLLOW = {};
  const nonterms = Object.keys(prods);
  const nonterminalsSet = new Set(nonterms);
  for (const A of nonterms) FOLLOW[A] = new Set();
  if (startSymbol && FOLLOW[startSymbol]) FOLLOW[startSymbol].add('$');

  let changed = true;
  while (changed) {
    changed = false;
    for (const A of nonterms) {
      for (const rhs of prods[A]) {
        for (let i = 0; i < rhs.length; i++) {
          const B = rhs[i];
          if (!nonterminalsSet.has(B)) continue; // skip terminals

          const beta = rhs.slice(i + 1);
          if (beta.length > 0) {
            const fb = firstOfString(beta, FIRST, nonterminalsSet);
            // everything in FIRST(beta) except ε goes to FOLLOW(B)
            for (const t of fb) {
              if (t !== 'ε' && !FOLLOW[B].has(t)) {
                FOLLOW[B].add(t);
                changed = true;
              }
            }
            // if FIRST(beta) contains ε, add FOLLOW(A) to FOLLOW(B)
            if (fb.has('ε')) {
              for (const t of FOLLOW[A]) {
                if (!FOLLOW[B].has(t)) {
                  FOLLOW[B].add(t);
                  changed = true;
                }
              }
            }
          } else {
            // B at end: everything in FOLLOW(A) goes to FOLLOW(B)
            for (const t of FOLLOW[A]) {
              if (!FOLLOW[B].has(t)) {
                FOLLOW[B].add(t);
                changed = true;
              }
            }
          }
        }
      }
    }
  }
  return FOLLOW;
}

/* ------- LL(1) predictive table ------- */
function buildPredictiveTable(prods, FIRST, FOLLOW) {
  const table = {};
  const conflicts = [];
  const nonterms = Object.keys(prods);
  const nontermSet = new Set(nonterms);
  // gather terminal set
  const terminals = new Set();
  for (const A of nonterms) {
    table[A] = {};
    for (const rhs of prods[A]) {
      const fs = firstOfString(rhs, FIRST, nontermSet);
      for (const t of fs) if (t !== 'ε') terminals.add(t);
      if (fs.has('ε')) {
        for (const f of (FOLLOW[A] || new Set())) terminals.add(f);
      }
    }
  }
  // fill table
  for (const A of nonterms) {
    for (const rhs of prods[A]) {
      const fs = firstOfString(rhs, FIRST, nontermSet);
      for (const t of fs) {
        if (t === 'ε') continue;
        table[A][t] = table[A][t] || [];
        table[A][t].push(rhs);
      }
      if (fs.has('ε')) {
        for (const b of (FOLLOW[A] || new Set())) {
          table[A][b] = table[A][b] || [];
          table[A][b].push(rhs);
        }
      }
    }
  }
  // detect conflicts
  for (const A of nonterms) {
    for (const [t, list] of Object.entries(table[A])) {
      if (list.length > 1) {
        conflicts.push({ nonterminal: A, terminal: t, prods: list });
      }
    }
  }
  return { table, conflicts, terminals: Array.from(terminals).sort() };
}

/* ------- left recursion elimination ------- */
function eliminateLeftRecursion(prods0) {
  const prods = {};
  for (const k of Object.keys(prods0)) prods[k] = prods0[k].map(r => r.slice());
  const nonterms = Object.keys(prods);
  for (let i = 0; i < nonterms.length; i++) {
    const Ai = nonterms[i];
    for (let j = 0; j < i; j++) {
      const Aj = nonterms[j];
      const newR = [];
      for (const rhs of prods[Ai]) {
        if (rhs[0] === Aj) {
          for (const delta of prods[Aj]) {
            const comb = delta.concat(rhs.slice(1));
            newR.push(comb.length ? comb : ['ε']);
          }
        } else newR.push(rhs);
      }
      prods[Ai] = newR;
    }
    // eliminate immediate left recursion for Ai
    const alphas = [], betas = [];
    for (const rhs of prods[Ai]) {
      if (rhs[0] === Ai) alphas.push(rhs.slice(1).length ? rhs.slice(1) : ['ε']);
      else betas.push(rhs);
    }
    if (alphas.length > 0) {
      let prime = Ai + "'";
      while (prods[prime]) prime += "'";
      prods[prime] = [];
      const newAi = [];
      for (const b of betas) {
        if (b.length === 1 && b[0] === 'ε') newAi.push([prime]);
        else newAi.push(b.concat([prime]));
      }
      prods[Ai] = newAi.length ? newAi : [[prime]];
      for (const a of alphas) {
        if (a.length === 1 && a[0] === 'ε') prods[prime].push([prime]);
        else prods[prime].push(a.concat([prime]));
      }
      prods[prime].push(['ε']);
      nonterms.push(prime);
    }
  }
  return prods;
}

/* ------- left factoring ------- */
function leftFactor(prods0) {
  let prods = {};
  for (const k of Object.keys(prods0)) prods[k] = prods0[k].map(r => r.slice());
  let changed = true;
  while (changed) {
    changed = false;
    for (const A of Object.keys(prods)) {
      const rhss = prods[A];
      if (rhss.length < 2) continue;
      // group by first token
      const groups = {};
      for (const rhs of rhss) {
        const key = rhs[0] !== undefined ? rhs[0] : 'ε';
        (groups[key] = groups[key] || []).push(rhs);
      }
      let factored = false;
      for (const key of Object.keys(groups)) {
        const g = groups[key];
        if (g.length <= 1) continue;
        // compute longest common prefix
        let prefix = g[0].slice();
        for (let i = 1; i < g.length; i++) {
          const other = g[i];
          let k = 0;
          while (k < prefix.length && k < other.length && prefix[k] === other[k]) k++;
          prefix = prefix.slice(0, k);
          if (prefix.length === 0) break;
        }
        if (prefix.length === 0) continue;
        let prime = A + "_fact";
        while (prods[prime]) prime += "_";
        const newA = [];
        const factR = [];
        for (const rhs of rhss) {
          let matches = rhs.length >= prefix.length;
          for (let z = 0; z < prefix.length && matches; z++) {
            if (rhs[z] !== prefix[z]) matches = false;
          }
          if (matches) {
            const rest = rhs.slice(prefix.length);
            factR.push(rest.length ? rest : ['ε']);
          } else newA.push(rhs);
        }
        newA.push(prefix.concat([prime]));
        prods[A] = newA;
        prods[prime] = factR;
        changed = true;
        factored = true;
        break;
      }
      if (factored) break;
    }
  }
  return prods;
}

/* ------- regex testing ------- */
function testRegex(pattern, text) {
  try {
    const re = new RegExp(pattern, 'g');
    const matches = Array.from(text.matchAll(re)).map(m => ({
      text: m[0],
      index: m.index
    }));
    return { matches };
  } catch (e) {
    return { error: e.message };
  }
}

/* ------- rendering helpers ------- */
function setPrettySet(s) {
  if (!s) return '∅';
  const arr = Array.isArray(s) ? s.slice() : Array.from(s);
  if (arr.length === 0) return '∅';
  return '{ ' + arr.join(', ') + ' }';
}

function renderFirstFollow(prods, FIRST, FOLLOW) {
  const sym = identifySymbols(prods);
  const rows = sym.nonterminals.map(A => {
    const f = setPrettySet(FIRST[A]);
    const fo = setPrettySet(FOLLOW[A]);
    return `<tr><td style="padding:8px;border-bottom:1px solid #f1f1f1"><strong>${escapeHtml(A)}</strong></td><td style="padding:8px;border-bottom:1px solid #f1f1f1">${escapeHtml(f)}</td><td style="padding:8px;border-bottom:1px solid #f1f1f1">${escapeHtml(fo)}</td></tr>`;
  }).join('');
  const start = escapeHtml(sym.start || '-');
  return `<div style="margin-bottom:10px"><strong>Start symbol:</strong> ${start}</div>
    <table style="width:100%;border-collapse:collapse"><thead><tr style="text-align:left"><th>Nonterminal</th><th>FIRST</th><th>FOLLOW</th></tr></thead><tbody>${rows}</tbody></table>`;
}

function renderTransformedGrammar(prods) {
  return `<pre style="margin:0">${escapeHtml(stringifyGrammar(prods))}</pre>`;
}

function renderPredictiveTable(tableObj) {
  const table = tableObj.table;
  const nonterms = Object.keys(table);
  const termSet = new Set(tableObj.terminals || []);
  termSet.add('$');
  const termList = Array.from(termSet).sort((a,b)=> a < b ? -1 : a > b ? 1 : 0);

  let html = '<table style="width:100%;border-collapse:collapse"><thead><tr><th>NT \\ t</th>';
  for (const t of termList) html += `<th style="padding:6px;border-bottom:1px solid #eee">${escapeHtml(t)}</th>`;
  html += '</tr></thead><tbody>';

  for (const A of nonterms) {
    html += `<tr><td style="padding:8px;border-bottom:1px solid #f1f1f1"><strong>${escapeHtml(A)}</strong></td>`;
    for (const t of termList) {
      const cell = table[A][t];
      if (!cell || cell.length === 0) html += '<td style="padding:10px;border-bottom:1px solid #f9f9f9">-</td>';
      else {
        const txt = cell.map(r => `${A} → ${r.join(' ')}`).join('<br>');
        html += `<td style="padding:10px;border-bottom:1px solid #f9f9f9">${escapeHtml(txt)}</td>`;
      }
    }
    html += '</tr>';
  }
  html += '</tbody></table>';
  return html;
}

function renderConflicts(conflicts) {
  if (!conflicts || conflicts.length === 0) {
    return '<div style="margin-top:10px;color:#16a34a"><strong>No conflicts — grammar appears LL(1).</strong></div>';
  }
  let html = '<div style="margin-top:10px;color:#b91c1c"><strong>Conflicts:</strong><pre>';
  html += conflicts.map(c => `NT ${c.nonterminal} on ${c.terminal}: ${c.prods.map(p => p.join(' ')).join(' || ')}`).join('\n');
  html += '</pre></div>';
  return html;
}

/* ------- Optional UI wiring (same IDs as before) ------- */
document.addEventListener('DOMContentLoaded', () => {
  // tab wiring (if present)
  const tabs = Array.from(document.querySelectorAll('.tab'));
  const panels = Array.from(document.querySelectorAll('.tab-panel'));
  tabs.forEach(btn => btn.addEventListener('click', () => {
    tabs.forEach(b => b.classList.remove('active'));
    btn.classList.add('active');
    panels.forEach(p => p.classList.remove('active'));
    const id = btn.dataset.tab + '-panel';
    const el = document.getElementById(id);
    if (el) el.classList.add('active');
  }));

  // FIRST & FOLLOW
  const e1 = document.getElementById('example-first');
  if (e1) e1.addEventListener('click', () => {
    const el = document.getElementById('grammar-first');
    if (el) el.value =
`E -> T E'
E' -> + T E' | ε
T -> F T'
T' -> * F T' | ε
F -> ( E ) | id`;
    toast('Example loaded');
  });
  const c1 = document.getElementById('compute-first');
  if (c1) c1.addEventListener('click', () => {
    const rawEl = document.getElementById('grammar-first');
    const outEl = document.getElementById('first-output');
    if (!rawEl || !outEl) { toast('Missing UI'); return; }
    const raw = rawEl.value.trim();
    if (!raw) { toast('Enter grammar'); return; }
    const prods = parseGrammar(raw);
    if (Object.keys(prods).length === 0) { toast('Could not parse grammar'); return; }
    const FIRST = computeFirst(prods);
    const FOLLOW = computeFollow(prods, FIRST, identifySymbols(prods).start);
    outEl.innerHTML = renderFirstFollow(prods, FIRST, FOLLOW);
  });

  // Left recursion example/run
  const exLR = document.getElementById('example-leftrec');
  if (exLR) exLR.addEventListener('click', () => {
    const g = document.getElementById('grammar-leftrec');
    if (g) g.value =
`S -> S a | b
A -> A c | d`;
    toast('Example loaded');
  });
  const runLR = document.getElementById('run-leftrec');
  if (runLR) runLR.addEventListener('click', () => {
    const rawEl = document.getElementById('grammar-leftrec');
    const outEl = document.getElementById('leftrec-output');
    if (!rawEl || !outEl) { toast('Missing UI'); return; }
    const raw = rawEl.value.trim(); if (!raw) { toast('Enter grammar'); return; }
    const prods = parseGrammar(raw);
    const res = eliminateLeftRecursion(prods);
    outEl.innerHTML = renderTransformedGrammar(res);
  });

  // Left factoring example/run
  const exLF = document.getElementById('example-leftfact');
  if (exLF) exLF.addEventListener('click', () => {
    const g = document.getElementById('grammar-leftfact');
    if (g) g.value = `S -> a b c | a b d | e`;
    toast('Example loaded');
  });
  const runLF = document.getElementById('run-leftfact');
  if (runLF) runLF.addEventListener('click', () => {
    const rawEl = document.getElementById('grammar-leftfact');
    const outEl = document.getElementById('leftfact-output');
    if (!rawEl || !outEl) { toast('Missing UI'); return; }
    const raw = rawEl.value.trim(); if (!raw) { toast('Enter grammar'); return; }
    const prods = parseGrammar(raw);
    const res = leftFactor(prods);
    outEl.innerHTML = renderTransformedGrammar(res);
  });

  // LL(1)
  const exLL = document.getElementById('example-ll1');
  if (exLL) exLL.addEventListener('click', () => {
    const g = document.getElementById('grammar-ll1');
    if (g) g.value =
`E -> T E'
E' -> + T E' | ε
T -> F T'
T' -> * F T' | ε
F -> ( E ) | id`;
    toast('Example loaded');
  });
  const runLL = document.getElementById('run-ll1');
  if (runLL) runLL.addEventListener('click', () => {
    const rawEl = document.getElementById('grammar-ll1');
    const outEl = document.getElementById('ll1-output');
    if (!rawEl || !outEl) { toast('Missing UI'); return; }
    const raw = rawEl.value.trim(); if (!raw) { toast('Enter grammar'); return; }
    const prods = parseGrammar(raw);
    const FIRST = computeFirst(prods);
    const FOLLOW = computeFollow(prods, FIRST, identifySymbols(prods).start);
    const tableObj = buildPredictiveTable(prods, FIRST, FOLLOW);
    let html = '<div style="margin-bottom:8px"><strong>FIRST &amp; FOLLOW</strong></div>';
    html += renderFirstFollow(prods, FIRST, FOLLOW);
    html += '<div style="margin-top:12px"><strong>Predictive table</strong></div>';
    html += renderPredictiveTable(tableObj);
    html += renderConflicts(tableObj.conflicts);
    outEl.innerHTML = html;
  });

  // Regex example/run
  const exR = document.getElementById('example-regex');
  if (exR) exR.addEventListener('click', () => {
    const p = document.getElementById('regex-pattern');
    const t = document.getElementById('regex-text');
    if (p) p.value = 'a(b|c)+';
    if (t) t.value = 'test abc abb acbc aXc';
    toast('Example loaded');
  });
  const runR = document.getElementById('run-regex');
  if (runR) runR.addEventListener('click', () => {
    const patEl = document.getElementById('regex-pattern');
    const textEl = document.getElementById('regex-text');
    const outH = document.getElementById('regex-highlight');
    const outL = document.getElementById('regex-list');
    if (!patEl || !textEl || !outH || !outL) { toast('Missing UI'); return; }
    const pat = patEl.value.trim();
    const txt = textEl.value || '';
    if (!pat) { toast('Enter regex pattern'); return; }
    const res = testRegex(pat, txt);
    if (res.error) {
      outH.textContent = 'Error: ' + res.error;
      outL.innerHTML = '';
      return;
    }
    const matches = res.matches;
    outH.innerHTML = (() => {
      if (!txt) return '<div class="muted">No text</div>';
      if (!matches || matches.length === 0) return '<div class="muted">No matches</div>';
      let last = 0, html = '';
      for (const m of matches) {
        html += escapeHtml(txt.slice(last, m.index));
        html += `<span style="background:#fdecec;border-radius:6px;padding:2px 6px;margin:0 4px;color:#9b1c1c">${escapeHtml(m.text)}</span>`;
        last = m.index + m.text.length;
      }
      html += escapeHtml(txt.slice(last));
      html += `<div style="margin-top:10px;color:#6b7280">Total matches: ${matches.length}</div>`;
      return html;
    })();
    outL.innerHTML = (matches || []).map(m => `<div style="display:flex;justify-content:space-between;padding:8px;background:#f3f4f6;border-radius:6px;margin-bottom:8px"><div>${escapeHtml(m.text)}</div><div style="color:#6b7280">[${m.index}, ${m.index + m.text.length - 1}]</div></div>`).join('');
  });
});
