/* =========================================
   1. UTILITIES
   ========================================= */
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
    fontSize: '13px',
    boxShadow: '0 4px 6px rgba(0,0,0,0.1)'
  });
  document.body.appendChild(el);
  setTimeout(() => el.remove(), 2000);
}

function escapeHtml(s) {
  return (s + '')
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;');
}
/* =========================================
 2. TOKENIZER & PARSER (MASTER VERSION)
 ========================================= */
const TOKEN_RE = /ε|epsilon|id|[A-Z](?:_[a-zA-Z0-9]+|')*|[a-z0-9]|(==|!=|<=|>=|\|\||&&|[(){}\[\]+*\/\\^=,.:;<>|$!-])/g;

function tokenizeRHS(alt) {
  alt = (alt || '').trim();
  if (!alt) return ['ε'];
  if (alt === 'ε' || alt.toLowerCase() === 'epsilon') return ['ε'];

  // 1. Trust spaces if user provided them (e.g. "A C B")
  if (alt.includes(' ')) {
    return alt.split(/\s+/);
  }

  // 2. Otherwise use the Master Regex to split intelligently
  const tokens = [];
  let m;
  TOKEN_RE.lastIndex = 0;
  while ((m = TOKEN_RE.exec(alt)) !== null) {
    tokens.push(m[0]);
  }

  return tokens.length ? tokens : ['ε'];
}

function parseGrammar(text) {
  const lines = String(text || '').split('\n').map(l => l.trim()).filter(Boolean);
  const prods = {};

  for (const line of lines) {
    let idx = line.indexOf('->');
    if (idx === -1) idx = line.indexOf('→');
    if (idx === -1) continue;

    const lhs = line.slice(0, idx).trim();
    const rhs = line.slice(idx + 2).trim();
    const alts = rhs.split('|').map(a => a.trim());

    if (!prods[lhs]) prods[lhs] = [];

    for (const alt of alts) {
      // The parser tokenizes immediately. 
      // All algorithms downstream will receive clean arrays.
      prods[lhs].push(tokenizeRHS(alt));
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
        if (t === 'ε' || t === 'epsilon') continue;
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

/* =========================================
  3. ALGORITHMS: FIRST & FOLLOW (OPTIMIZED)
  ========================================= */

function firstOfString(tokens, FIRST, nonterminalsSet) {
  const res = new Set();
  let allNullable = true;

  for (const sym of tokens) {
    if (sym === 'ε' || sym === 'epsilon') continue;

    // 1. If Terminal, add it and stop
    if (!nonterminalsSet.has(sym)) {
      res.add(sym);
      allNullable = false;
      break;
    }

    // 2. If Non-Terminal, add its FIRST set (excluding epsilon)
    const fset = FIRST[sym] || new Set();
    for (const t of fset) {
      if (t !== 'ε' && t !== 'epsilon') res.add(t);
    }

    // 3. If this Non-Terminal is NOT nullable, stop here
    if (!fset.has('ε') && !fset.has('epsilon')) {
      allNullable = false;
      break;
    }
    // If it WAS nullable, loop continues to next symbol...
  }

  if (allNullable) res.add('ε');
  return res;
}

function computeFirst(prods) {
  const FIRST = {};
  const nonterms = Object.keys(prods);
  const nonterminalsSet = new Set(nonterms);

  for (const A of nonterms) FIRST[A] = new Set();

  let changed = true;
  while (changed) {
    changed = false;
    for (const A of nonterms) {
      for (const rhs of prods[A]) {
        const initialSize = FIRST[A].size;
        const stringFirst = firstOfString(rhs, FIRST, nonterminalsSet);

        for (const t of stringFirst) {
          if (!FIRST[A].has(t)) FIRST[A].add(t);
        }
        if (FIRST[A].size > initialSize) changed = true;
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

  if (startSymbol && nonterminalsSet.has(startSymbol)) {
    FOLLOW[startSymbol].add('$');
  }

  let changed = true;
  while (changed) {
    changed = false;
    for (const A of nonterms) {
      for (const rhs of prods[A]) {
        for (let i = 0; i < rhs.length; i++) {
          const B = rhs[i];
          if (!nonterminalsSet.has(B)) continue;

          const beta = rhs.slice(i + 1);
          const trailer = (beta.length > 0) ? firstOfString(beta, FIRST, nonterminalsSet) : null;

          // Rule 2: Follow(B) += First(beta) - {ε}
          if (trailer) {
            for (const t of trailer) {
              if (t !== 'ε' && t !== 'epsilon' && !FOLLOW[B].has(t)) {
                FOLLOW[B].add(t);
                changed = true;
              }
            }
          }

          // Rule 3: Follow(B) += Follow(A)
          if (!trailer || trailer.has('ε') || trailer.has('epsilon')) {
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
/* =========================================
   4. ALGORITHM: LL(1) TABLE
   ========================================= */

function buildPredictiveTable(prods, FIRST, FOLLOW) {
  const table = {};
  const conflicts = [];
  const nonterms = Object.keys(prods);
  const nontermSet = new Set(nonterms);

  // Identify all Terminals for table headers
  const terminals = new Set();
  for (const A of nonterms) {
    table[A] = {};
    for (const rhs of prods[A]) {
      for (const t of rhs) {
        if (!nontermSet.has(t) && t !== 'ε') terminals.add(t);
      }
    }
    // Include sync tokens from Follow set
    if (FOLLOW[A]) {
      for (const t of FOLLOW[A]) {
        if (t !== '$') terminals.add(t);
      }
    }
  }

  for (const A of nonterms) {
    for (const rhs of prods[A]) {
      const fs = firstOfString(rhs, FIRST, nontermSet);

      // 1. For terminal 'a' in First(alpha), add A -> alpha
      for (const t of fs) {
        if (t !== 'ε') {
          table[A][t] = table[A][t] || [];
          // Avoid duplicate insertion of exact same rule
          if (!table[A][t].some(r => r.join(' ') === rhs.join(' '))) {
            table[A][t].push(rhs);
          }
        }
      }

      // 2. If epsilon in First(alpha), add A -> alpha for 'b' in Follow(A)
      if (fs.has('ε')) {
        for (const b of FOLLOW[A]) {
          table[A][b] = table[A][b] || [];
          if (!table[A][b].some(r => r.join(' ') === rhs.join(' '))) {
            table[A][b].push(rhs);
          }
        }
      }
    }
  }

  // Detect Conflicts
  for (const A of nonterms) {
    for (const t of Object.keys(table[A])) {
      if (table[A][t].length > 1) {
        conflicts.push({ nonterminal: A, terminal: t, prods: table[A][t] });
      }
    }
  }

  return { table, conflicts, terminals: Array.from(terminals).sort() };
}

/* =========================================
   5. ALGORITHM: LEFT RECURSION
   ========================================= */

function eliminateLeftRecursion(prods0) {
  const prods = {};
  // Deep copy
  for (const k of Object.keys(prods0)) prods[k] = prods0[k].map(r => r.slice());

  const nonterms = Object.keys(prods);

  for (let i = 0; i < nonterms.length; i++) {
    const Ai = nonterms[i];

    // Step 1: Eliminate Indirect Recursion
    for (let j = 0; j < i; j++) {
      const Aj = nonterms[j];
      const newR = [];

      for (const rhs of prods[Ai]) {
        if (rhs[0] === Aj) {
          // Ai -> Aj gamma
          const gamma = rhs.slice(1);
          // Substitute Aj -> delta
          for (const delta of prods[Aj]) {
            // CORNER CASE: If delta is epsilon, result is just gamma
            let effectiveDelta = (delta.length === 1 && delta[0] === 'ε') ? [] : delta;

            // Combine
            let combined = effectiveDelta.concat(gamma);
            if (combined.length === 0) combined = ['ε'];

            newR.push(combined);
          }
        } else {
          newR.push(rhs);
        }
      }
      prods[Ai] = newR;
    }

    // Step 2: Eliminate Immediate Recursion
    const alphas = [];
    const betas = [];

    for (const rhs of prods[Ai]) {
      if (rhs[0] === Ai) {
        // Recursive: Ai -> Ai alpha
        const alpha = rhs.slice(1);
        alphas.push(alpha.length ? alpha : ['ε']);
      } else {
        betas.push(rhs);
      }
    }

    if (alphas.length > 0) {
      let prime = Ai + "'";
      while (prods[prime]) prime += "'";

      prods[prime] = [];
      const newAi = [];

      // A -> beta A'
      for (const b of betas) {
        // CORNER CASE: If beta is epsilon, result is just A'
        let cleanB = (b.length === 1 && b[0] === 'ε') ? [] : b;
        newAi.push(cleanB.concat([prime]));
      }
      prods[Ai] = newAi;

      // A' -> alpha A' | epsilon
      for (const a of alphas) {
        let cleanA = (a.length === 1 && a[0] === 'ε') ? [] : a;
        prods[prime].push(cleanA.concat([prime]));
      }
      prods[prime].push(['ε']);

      nonterms.push(prime);
    }
  }
  return prods;
}

/* =========================================
   6. ALGORITHM: LEFT FACTORING (SINGLE PASS)
   ========================================= */

function leftFactor(prods0) {
  // Deep copy the grammar (it is already tokenized by Block 1)
  let prods = {};
  for (const k of Object.keys(prods0)) {
    prods[k] = prods0[k].map(rhs => [...rhs]);
  }

  const originalNonTerms = Object.keys(prods);

  for (const A of originalNonTerms) {
    const rhss = prods[A];
    if (rhss.length < 2) continue;

    // Group by First Symbol
    const groups = {};
    for (const rhs of rhss) {
      if (rhs.length === 0) continue;
      const firstSym = rhs[0];
      if (!groups[firstSym]) groups[firstSym] = [];
      groups[firstSym].push(rhs);
    }

    // Process Groups
    for (const key of Object.keys(groups)) {
      const group = groups[key];

      if (group.length > 1) {
        // Find Longest Common Prefix
        let prefix = group[0].slice();
        for (let i = 1; i < group.length; i++) {
          const current = group[i];
          let k = 0;
          while (k < prefix.length && k < current.length && prefix[k] === current[k]) {
            k++;
          }
          prefix = prefix.slice(0, k);
          if (prefix.length === 0) break;
        }

        if (prefix.length > 0) {
          // Generate new Name
          let prime = A + "_fact";
          let counter = 1;
          while (prods[prime]) { prime = A + "_fact" + counter++; }

          // Update A
          const newA = prods[A].filter(r => !group.includes(r));
          newA.push([...prefix, prime]);
          prods[A] = newA;

          // Create New Rule (S_fact)
          const newPrime = [];
          for (const r of group) {
            const remainder = r.slice(prefix.length);
            newPrime.push(remainder.length ? remainder : ['ε']);
          }
          prods[prime] = newPrime;

          // STOP: We do not loop back, so we only factor one level deep.
        }
      }
    }
  }
  return prods;
}
/* =========================================
   7. REGEX ENGINE & MATCHING
   ========================================= */

function testRegex(pattern, text) {
  try {
    const re = new RegExp(pattern, 'g');
    // matchAll is safer/more detailed than match
    const matches = Array.from(text.matchAll(re)).map(m => ({
      text: m[0],
      index: m.index
    }));
    return { matches };
  } catch (e) {
    return { error: e.message };
  }
}

/* =========================================
   8. RENDERING HELPERS
   ========================================= */

function setPrettySet(s) {
  if (!s || s.size === 0) return '∅';
  return '{ ' + Array.from(s).join(', ') + ' }';
}

function renderFirstFollow(prods, FIRST, FOLLOW) {
  const sym = identifySymbols(prods);
  const rows = sym.nonterminals.map(A => {
    return `<tr>
      <td style="padding:8px;border-bottom:1px solid #eee"><strong>${escapeHtml(A)}</strong></td>
      <td style="padding:8px;border-bottom:1px solid #eee;color:#059669">${escapeHtml(setPrettySet(FIRST[A]))}</td>
      <td style="padding:8px;border-bottom:1px solid #eee;color:#d97706">${escapeHtml(setPrettySet(FOLLOW[A]))}</td>
    </tr>`;
  }).join('');

  return `<table style="width:100%;border-collapse:collapse;font-family:monospace;font-size:14px;">
    <thead><tr style="background:#f3f4f6;text-align:left">
      <th style="padding:8px">Nonterminal</th>
      <th style="padding:8px">FIRST</th>
      <th style="padding:8px">FOLLOW</th>
    </tr></thead>
    <tbody>${rows}</tbody>
  </table>`;
}

function renderTransformedGrammar(prods) {
  return `<pre style="background:#f8fafc;padding:15px;border:1px solid #e2e8f0;border-radius:6px;font-family:monospace;color:#334155">${escapeHtml(stringifyGrammar(prods))}</pre>`;
}

function renderPredictiveTable(tableObj) {
  const table = tableObj.table;
  const nonterms = Object.keys(table);
  const termList = (tableObj.terminals || []).concat(['$']);

  let html = '<div style="overflow-x:auto"><table style="width:100%;border-collapse:collapse;font-size:13px;font-family:monospace;"><thead><tr style="background:#f3f4f6">';
  html += '<th style="padding:8px;border:1px solid #e5e7eb">NT</th>';
  for (const t of termList) html += `<th style="padding:8px;border:1px solid #e5e7eb;min-width:40px">${escapeHtml(t)}</th>`;
  html += '</tr></thead><tbody>';

  for (const A of nonterms) {
    html += `<tr><td style="padding:8px;border:1px solid #e5e7eb;font-weight:bold;background:#fff">${escapeHtml(A)}</td>`;
    for (const t of termList) {
      const cell = table[A][t];
      html += '<td style="padding:8px;border:1px solid #e5e7eb;background:#fff">';
      if (cell && cell.length > 0) {
        html += cell.map(r => `<div style="white-space:nowrap;color:#2563eb">${A} → ${r.join(' ')}</div>`).join('');
      }
      html += '</td>';
    }
    html += '</tr>';
  }
  html += '</tbody></table></div>';
  return html;
}

function renderConflicts(conflicts) {
  if (!conflicts || conflicts.length === 0) {
    return '<div style="margin-top:15px;padding:12px;background:#dcfce7;color:#166534;border-radius:6px;border:1px solid #bbf7d0"><strong>✅ Grammar is LL(1). No conflicts found.</strong></div>';
  }
  let html = '<div style="margin-top:15px;padding:12px;background:#fee2e2;color:#991b1b;border-radius:6px;border:1px solid #fecaca"><strong>⚠️ Conflicts Detected (Not LL(1)):</strong><ul style="margin:5px 0 0 15px;padding:0">';
  html += conflicts.map(c => `<li>On <strong>${escapeHtml(c.nonterminal)}</strong>, input <strong>${escapeHtml(c.terminal)}</strong>: ${c.prods.map(p => escapeHtml(p.join(' '))).join(' <strong>OR</strong> ')}</li>`).join('');
  html += '</ul></div>';
  return html;
}

/* =========================================
   9. UI EVENT BINDING
   ========================================= */

document.addEventListener('DOMContentLoaded', () => {

  const get = (id) => document.getElementById(id);

  // Tab Logic
  document.querySelectorAll('.tab').forEach(btn => {
    btn.addEventListener('click', () => {
      document.querySelectorAll('.tab').forEach(b => b.classList.remove('active'));
      document.querySelectorAll('.tab-panel').forEach(p => p.classList.remove('active'));
      btn.classList.add('active');
      const p = get(btn.dataset.tab + '-panel');
      if (p) p.classList.add('active');
    });
  });

  // 1. First & Follow
  const btnExFF = get('example-first');
  if (btnExFF) btnExFF.addEventListener('click', () => {
    const el = get('grammar-first');
    if (el) el.value = "S -> ACB | Cbb | Ba\nA -> da | BC\nB -> g | ε\nC -> h | ε";
    toast("Example Loaded");
  });

  const btnRunFF = get('compute-first');
  if (btnRunFF) btnRunFF.addEventListener('click', () => {
    const el = get('grammar-first');
    const out = get('first-output');
    if (!el || !out) return;
    const raw = el.value.trim();
    if (!raw) return toast("Please enter a grammar");
    const prods = parseGrammar(raw);
    if (Object.keys(prods).length === 0) return toast("Invalid Grammar");
    const FIRST = computeFirst(prods);
    const FOLLOW = computeFollow(prods, FIRST, identifySymbols(prods).start);
    out.innerHTML = renderFirstFollow(prods, FIRST, FOLLOW);
  });

  // 2. Left Recursion
  const btnExLR = get('example-leftrec');
  if (btnExLR) btnExLR.addEventListener('click', () => {
    const el = get('grammar-leftrec');
    if (el) el.value = "E -> E + T | T\nT -> T * F | F\nF -> ( E ) | id";
    toast("Example Loaded");
  });

  const btnRunLR = get('run-leftrec');
  if (btnRunLR) btnRunLR.addEventListener('click', () => {
    const el = get('grammar-leftrec');
    const out = get('leftrec-output');
    if (!el || !out) return;
    const prods = parseGrammar(el.value);
    if (Object.keys(prods).length === 0) return toast("Invalid Grammar");
    const res = eliminateLeftRecursion(prods);
    out.innerHTML = renderTransformedGrammar(res);
  });

  // 3. Left Factoring
  const btnExLF = get('example-leftfact');
  if (btnExLF) btnExLF.addEventListener('click', () => {
    const el = get('grammar-leftfact');
    if (el) el.value = "S ->bSSaaS | bSSaSb | bSb | a";
    toast("Example Loaded");
  });

  const btnRunLF = get('run-leftfact');
  if (btnRunLF) btnRunLF.addEventListener('click', () => {
    const el = get('grammar-leftfact');
    const out = get('leftfact-output');
    if (!el || !out) return;
    const prods = parseGrammar(el.value);
    if (Object.keys(prods).length === 0) return toast("Invalid Grammar");
    const res = leftFactor(prods);
    out.innerHTML = renderTransformedGrammar(res);
  });

  // 4. LL(1) Table
  const btnExLL = get('example-ll1');
  if (btnExLL) btnExLL.addEventListener('click', () => {
    const el = get('grammar-ll1');
    if (el) el.value = "E -> T E'\nE' -> + T E' | ε\nT -> F T'\nT' -> * F T' | ε\nF -> ( E ) | id";
    toast("Example (Conflict) Loaded");
  });

  const btnRunLL = get('run-ll1');
  if (btnRunLL) btnRunLL.addEventListener('click', () => {
    const el = get('grammar-ll1');
    const out = get('ll1-output');
    if (!el || !out) return;
    const prods = parseGrammar(el.value);
    if (Object.keys(prods).length === 0) return toast("Invalid Grammar");
    const FIRST = computeFirst(prods);
    const FOLLOW = computeFollow(prods, FIRST, identifySymbols(prods).start);
    const tableObj = buildPredictiveTable(prods, FIRST, FOLLOW);
    out.innerHTML = `
            <h4 style="margin:0 0 10px 0">First & Follow</h4>
            ${renderFirstFollow(prods, FIRST, FOLLOW)}
            <h4 style="margin:20px 0 10px 0">Predictive Parsing Table</h4>
            ${renderPredictiveTable(tableObj)}
            ${renderConflicts(tableObj.conflicts)}
        `;
  });

  // 5. Regex Tester
  const btnExReg = get('example-regex');
  if (btnExReg) btnExReg.addEventListener('click', () => {
    const p = get('regex-pattern');
    const t = get('regex-text');
    if (p) p.value = "a(b|c)+";
    if (t) t.value = "test abc abb acbc aXc";
    toast("Email Regex Loaded");
  });

  const btnRunReg = get('run-regex');
  if (btnRunReg) btnRunReg.addEventListener('click', () => {
    const pat = get('regex-pattern');
    const txt = get('regex-text');
    const outH = get('regex-highlight');
    const outL = get('regex-list');

    if (!pat || !txt || !outH) return;

    const textVal = txt.value;
    const res = testRegex(pat.value, textVal);

    if (res.error) {
      outH.innerHTML = `<div style="color:#ef4444;font-weight:bold">Error: ${res.error}</div>`;
      if (outL) outL.innerHTML = '';
      return;
    }

    const matches = res.matches;

    // Render Highlighted Text
    let html = '';
    let lastIdx = 0;

    if (matches.length === 0) {
      html = escapeHtml(textVal);
    } else {
      matches.forEach(m => {
        html += escapeHtml(textVal.substring(lastIdx, m.index));
        html += `<span style="background:#fde68a;color:#92400e;border-radius:2px;font-weight:bold">${escapeHtml(m.text)}</span>`;
        lastIdx = m.index + m.text.length;
      });
      html += escapeHtml(textVal.substring(lastIdx));
    }
    outH.innerHTML = `<div style="font-family:monospace;white-space:pre-wrap;background:#fff;padding:12px;border:1px solid #e5e7eb;border-radius:6px;min-height:50px">${html}</div>`;

    // Render Match List
    if (outL) {
      if (matches.length === 0) {
        outL.innerHTML = '<div style="color:#6b7280;margin-top:10px">No matches found.</div>';
      } else {
        const listHtml = matches.map((m, i) => `
                    <div style="display:flex;justify-content:space-between;padding:6px 10px;background:#f9fafb;border-bottom:1px solid #e5e7eb;font-size:13px;font-family:monospace">
                        <span><strong>#${i + 1}</strong>: ${escapeHtml(m.text)}</span>
                        <span style="color:#6b7280">Index: ${m.index}</span>
                    </div>
                `).join('');

        outL.innerHTML = `
                    <div style="margin-top:15px;border:1px solid #e5e7eb;border-radius:6px;overflow:hidden">
                        <div style="background:#f3f4f6;padding:8px 10px;font-weight:bold;font-size:13px;border-bottom:1px solid #e5e7eb">Match List (${matches.length})</div>
                        <div style="max-height:150px;overflow-y:auto">${listHtml}</div>
                    </div>
                `;
      }
    }
  });
});

/* =========================================
   10. EXTRA TOOLS: GRAMMAR VALIDATOR + NFA→DFA
   (APPEND ONLY – DO NOT CHANGE EXISTING CODE)
   ========================================= */

function validateGrammar(prods) {
  const nonterms = Object.keys(prods);
  const sym = identifySymbols(prods);
  const start = sym.start;
  const defined = new Set(nonterms);
  const used = new Set();

  // Collect which nonterminals appear on RHS
  for (const [A, rhss] of Object.entries(prods)) {
    for (const rhs of rhss) {
      for (const t of rhs) {
        if (defined.has(t)) {
          used.add(t);
        }
      }
    }
  }

  // Undefined nonterminals: used but never defined
  const undefinedNT = Array.from(used).filter(x => !defined.has(x));

  // Reachability from start
  const reachable = new Set();
  if (start && defined.has(start)) {
    const stack = [start];
    reachable.add(start);
    while (stack.length) {
      const A = stack.pop();
      const rhss = prods[A] || [];
      for (const rhs of rhss) {
        for (const t of rhs) {
          if (defined.has(t) && !reachable.has(t)) {
            reachable.add(t);
            stack.push(t);
          }
        }
      }
    }
  }

  const unreachable = nonterms.filter(A => !reachable.has(A));

  // Never-used: defined but never appears on any RHS (except maybe start)
  const neverUsed = nonterms.filter(A => !used.has(A) && A !== start);

  // ---------- PRODUCTIVE SYMBOL CHECK ----------
  // Productive = can derive a string of terminals (possibly ε)
  const terminalsSet = new Set(sym.terminals);
  const productive = new Set();

  let changed = true;
  while (changed) {
    changed = false;
    for (const [A, rhss] of Object.entries(prods)) {
      if (productive.has(A)) continue;

      for (const rhs of rhss) {
        // ε alone is productive
        if (rhs.length === 1 && (rhs[0] === 'ε' || rhs[0] === 'epsilon')) {
          productive.add(A);
          changed = true;
          break;
        }

        // Check if every symbol in RHS is either terminal or already productive
        let allGood = true;
        for (const s of rhs) {
          if (s === 'ε' || s === 'epsilon') continue;
          const isTerminal = terminalsSet.has(s) && !defined.has(s);
          const isProdNonterm = defined.has(s) && productive.has(s);
          if (!isTerminal && !isProdNonterm) {
            allGood = false;
            break;
          }
        }
        if (allGood) {
          productive.add(A);
          changed = true;
          break;
        }
      }
    }
  }

  const nonProductive = nonterms.filter(A => !productive.has(A));

  return {
    start,
    nonterminals: nonterms,
    terminals: sym.terminals,
    undefinedNT,
    unreachable,
    neverUsed,
    productive: Array.from(productive),
    nonProductive
  };
}


function renderGrammarValidationReport(rep) {
  const esc = escapeHtml;

  let html = `<div style="font-family:var(--font-mono, JetBrains Mono, monospace); font-size:13px;">`;

  // Summary
  html += `<div style="margin-bottom:12px;">
    <div><strong>Start Symbol:</strong> ${rep.start ? esc(rep.start) : '<em>Not detected</em>'}</div>
    <div><strong>Nonterminals:</strong> ${esc(rep.nonterminals.join(', ') || '—')}</div>
    <div><strong>Terminals:</strong> ${esc(rep.terminals.join(', ') || '—')}</div>
  </div>`;

  function section(title, items, okText) {
    if (!items || items.length === 0) {
      return `<div style="margin-bottom:10px;padding:8px 10px;border-radius:6px;background:#ecfdf3;color:#166534;border:1px solid #bbf7d0;">
        <strong>${esc(title)}:</strong> ${esc(okText)}
      </div>`;
    }
    return `<div style="margin-bottom:10px;padding:8px 10px;border-radius:6px;background:#fef2f2;color:#991b1b;border:1px solid #fecaca;">
      <strong>${esc(title)}:</strong>
      <ul style="margin:6px 0 0 18px; padding:0;">
        ${items.map(x => `<li style="margin:0;">${esc(x)}</li>`).join('')}
      </ul>
    </div>`;
  }

  html += section(
    'Undefined Nonterminals',
    rep.undefinedNT,
    'No undefined nonterminals found.'
  );

  html += section(
    'Unreachable Nonterminals (from start)',
    rep.unreachable,
    'All nonterminals are reachable from the start symbol.'
  );

  html += section(
    'Never-Used Nonterminals',
    rep.neverUsed,
    'Every nonterminal is used in some production.'
  );

  // NEW: Productive symbols report
  html += section(
    'Non-Productive Nonterminals',
    rep.nonProductive,
    'Every nonterminal can derive a string of terminals (possibly ε).'
  );

  html += `</div>`;
  return html;
}
/* =========================================
   SINGLE TOOL: NFA → DFA → MIN DFA
   ========================================= */

/* Parse NFA (robust) */
function parseNFACombined(text) {
  const lines = String(text || '')
    .split('\n')
    .map(l => l.trim())
    .filter(Boolean);

  const stateSet = new Set();
  const acceptSet = new Set();
  const alphaSet = new Set();
  const transitions = {};

  let statesList = [];
  let start = null;
  let inTrans = false;

  for (const line of lines) {
    if (/^states\s*:/i.test(line)) {
      statesList = line.split(':')[1]
        .split(',')
        .map(s => s.trim())
        .filter(Boolean);
      statesList.forEach(s => stateSet.add(s));
      continue;
    }
    if (/^alphabet\s*:/i.test(line)) {
      const parts = line.split(':')[1]
        .split(',')
        .map(s => s.trim())
        .filter(Boolean);
      parts.forEach(sym => {
        if (sym.toLowerCase() !== 'epsilon' && sym !== 'ε') {
          alphaSet.add(sym);
        }
      });
      continue;
    }
    if (/^start\s*:/i.test(line)) {
      start = line.split(':')[1].trim();
      if (start) stateSet.add(start);
      continue;
    }
    if (/^accept\s*:/i.test(line)) {
      line.split(':')[1]
        .split(',')
        .map(s => s.trim())
        .filter(Boolean)
        .forEach(s => {
          acceptSet.add(s);
          stateSet.add(s);
        });
      continue;
    }
    if (/^transitions\s*:/i.test(line)) {
      inTrans = true;
      continue;
    }

    if (inTrans) {
      // q0,a->q1,q2
      const parts = line.split('->');
      if (parts.length !== 2) continue;

      const left = parts[0].split(',');
      if (left.length !== 2) continue;

      const from = left[0].trim();
      let sym = left[1].trim();
      if (!from || !sym) continue;

      if (sym.toLowerCase() === 'epsilon' || sym === 'ε') {
        sym = 'ε';
      } else {
        alphaSet.add(sym);
      }

      const dests = parts[1]
        .split(',')
        .map(s => s.trim())
        .filter(Boolean);

      if (!dests.length) continue;

      stateSet.add(from);
      dests.forEach(d => stateSet.add(d));

      if (!transitions[from]) transitions[from] = {};
      if (!transitions[from][sym]) transitions[from][sym] = new Set();
      dests.forEach(d => transitions[from][sym].add(d));
    }
  }

  if (!statesList.length && stateSet.size) {
    statesList = Array.from(stateSet);
  }

  if (!statesList.length) {
    return { error: 'No states found. Please add "States: ..."' };
  }

  if (!start) {
    start = statesList[0];
  }

  const alphabet = Array.from(alphaSet);

  return {
    states: statesList,
    alphabet,
    start,
    accepts: Array.from(acceptSet),
    transitions
  };
}

/* ε-closure */
function epsilonClosureCombined(stateSet, transitions) {
  const stack = Array.from(stateSet);
  const closure = new Set(stateSet);

  while (stack.length) {
    const s = stack.pop();
    const eps = transitions[s] && transitions[s]['ε'];
    if (!eps) continue;
    for (const t of eps) {
      if (!closure.has(t)) {
        closure.add(t);
        stack.push(t);
      }
    }
  }
  return closure;
}

/* move for NFA */
function moveNFACombined(stateSet, sym, transitions) {
  const res = new Set();
  for (const s of stateSet) {
    const ts = transitions[s] && transitions[s][sym];
    if (!ts) continue;
    for (const t of ts) res.add(t);
  }
  return res;
}

/* NFA → DFA (subset construction) */
function nfaToDfaCombined(nfa) {
  if (nfa.error) return nfa;

  const { alphabet, start, accepts, transitions } = nfa;
  const symbols = (alphabet || []).slice();
  const acceptSet = new Set(accepts || []);

  function setName(set) {
    const arr = Array.from(set);
    arr.sort();
    return arr.join(',') || '∅';
  }

  const startClosure = epsilonClosureCombined(new Set([start]), transitions);
  const startName = setName(startClosure);

  const states = [];
  const dfaTrans = {};
  const dfaAccepts = new Set();
  const seen = {};
  const queue = [];

  seen[startName] = startClosure;
  states.push(startName);
  queue.push(startClosure);

  if (Array.from(startClosure).some(s => acceptSet.has(s))) {
    dfaAccepts.add(startName);
  }

  while (queue.length) {
    const curSet = queue.shift();
    const curName = setName(curSet);
    if (!dfaTrans[curName]) dfaTrans[curName] = {};

    for (const sym of symbols) {
      const moved = moveNFACombined(curSet, sym, transitions);
      if (!moved.size) continue;
      const closure = epsilonClosureCombined(moved, transitions);
      const name = setName(closure);

      if (!seen[name]) {
        seen[name] = closure;
        states.push(name);
        queue.push(closure);
        if (Array.from(closure).some(s => acceptSet.has(s))) {
          dfaAccepts.add(name);
        }
      }
      dfaTrans[curName][sym] = name;
    }
  }

  return {
    states,
    alphabet: symbols,
    start: startName,
    accepts: Array.from(dfaAccepts),
    transitions: dfaTrans
  };
}

/* Complete DFA with dead state */
function completeDFACombined(dfa) {
  if (dfa.error) return dfa;

  const { states, alphabet, start, accepts, transitions } = dfa;
  const newStates = states.slice();
  const newTrans = {};
  const acceptSet = new Set(accepts || []);

  let dead = '⊥';
  while (newStates.includes(dead)) dead += "'";

  let needDead = false;

  for (const s of states) {
    newTrans[s] = {};
    const tOld = transitions[s] || {};
    for (const a of alphabet) {
      if (tOld[a]) {
        newTrans[s][a] = tOld[a];
      } else {
        newTrans[s][a] = dead;
        needDead = true;
      }
    }
  }

  if (needDead) {
    newStates.push(dead);
    newTrans[dead] = {};
    for (const a of alphabet) {
      newTrans[dead][a] = dead;
    }
  }

  return {
    states: newStates,
    alphabet,
    start,
    accepts: Array.from(acceptSet),
    transitions: newTrans
  };
}

/* Remove unreachable states */
function removeUnreachableDFACombined(dfa) {
  if (dfa.error) return dfa;

  const { states, alphabet, start, accepts, transitions } = dfa;
  if (!start) return dfa;

  const reachable = new Set([start]);
  const stack = [start];

  while (stack.length) {
    const s = stack.pop();
    const trans = transitions[s] || {};
    for (const a of alphabet) {
      const to = trans[a];
      if (to && !reachable.has(to)) {
        reachable.add(to);
        stack.push(to);
      }
    }
  }

  const newStates = states.filter(s => reachable.has(s));
  const newAccepts = (accepts || []).filter(s => reachable.has(s));
  const newTrans = {};

  for (const s of newStates) {
    const tOld = transitions[s] || {};
    newTrans[s] = {};
    for (const a of alphabet) {
      const to = tOld[a];
      if (to && reachable.has(to)) {
        newTrans[s][a] = to;
      }
    }
  }

  return {
    states: newStates,
    alphabet,
    start,
    accepts: newAccepts,
    transitions: newTrans
  };
}

/* Minimize DFA via partition refinement */
function minimizeDFACombined(dfa0) {
  if (dfa0.error) return dfa0;

  const dfa = removeUnreachableDFACombined(dfa0);
  const { states, alphabet, start, accepts, transitions } = dfa;
  const acceptSet = new Set(accepts || []);

  if (!states.length) return { error: 'DFA has no states.' };

  const finals = states.filter(s => acceptSet.has(s));
  const nonFinals = states.filter(s => !acceptSet.has(s));

  let P = [];
  if (finals.length) P.push(new Set(finals));
  if (nonFinals.length) P.push(new Set(nonFinals));
  if (!P.length) return { error: 'No partition could be formed.' };

  function blockIndex(st, blocks) {
    for (let i = 0; i < blocks.length; i++) {
      if (blocks[i].has(st)) return i;
    }
    return -1;
  }

  let changed = true;
  while (changed) {
    changed = false;
    const newP = [];

    for (const block of P) {
      if (block.size <= 1) {
        newP.push(block);
        continue;
      }

      const groups = new Map();

      for (const s of block) {
        let sig = '';
        const trans = transitions[s] || {};
        for (const a of alphabet) {
          const to = trans[a] || null;
          const idx = to ? blockIndex(to, P) : -1;
          sig += a + ':' + idx + ';';
        }
        if (!groups.has(sig)) groups.set(sig, new Set());
        groups.get(sig).add(s);
      }

      if (groups.size === 1) {
        newP.push(block);
      } else {
        changed = true;
        for (const g of groups.values()) newP.push(g);
      }
    }

    P = newP;
  }

  const newStates = [];
  const className = new Map();

  for (const block of P) {
    const arr = Array.from(block).sort();
    const name = arr.join(',');
    newStates.push(name);
    arr.forEach(s => className.set(s, name));
  }

  const newStart = className.get(start);
  const newAccepts = new Set();

  for (const name of newStates) {
    const parts = name.split(',');
    if (parts.some(s => acceptSet.has(s))) {
      newAccepts.add(name);
    }
  }

  const newTrans = {};
  for (const block of P) {
    const arr = Array.from(block);
    const rep = arr[0];
    const repName = className.get(rep);
    newTrans[repName] = {};

    const trans = transitions[rep] || {};
    for (const a of alphabet) {
      const to = trans[a];
      if (to) newTrans[repName][a] = className.get(to);
    }
  }

  return {
    states: newStates,
    alphabet,
    start: newStart,
    accepts: Array.from(newAccepts),
    transitions: newTrans
  };
}

/* Render DFA table */
function renderDfaTableCombined(dfa) {
  if (dfa.error) {
    return `<div style="color:#b91c1c;font-weight:bold;">Error: ${escapeHtml(dfa.error)}</div>`;
  }

  const esc = escapeHtml;
  const symbols = dfa.alphabet || [];
  const accSet = new Set(dfa.accepts || []);

  let html = '<table style="width:100%;border-collapse:collapse;font-size:13px;">';
  html += '<thead><tr>';
  html += '<th style="padding:8px;border-bottom:1px solid #e2e8f0;">State</th>';
  symbols.forEach(sym => {
    html += `<th style="padding:8px;border-bottom:1px solid #e2e8f0;">on ${esc(sym)}</th>`;
  });
  html += '<th style="padding:8px;border-bottom:1px solid #e2e8f0;">Accepting?</th>';
  html += '</tr></thead><tbody>';

  dfa.states.forEach(st => {
    const isStart = st === dfa.start;
    const isAcc = accSet.has(st);
    const trans = dfa.transitions[st] || {};

    html += '<tr>';
    html += `<td style="padding:8px;border-bottom:1px solid #f1f5f9;font-weight:${isStart ? '700' : '500'};">`;
    if (isStart) html += '→ ';
    html += esc(st) + '</td>';

    symbols.forEach(sym => {
      const to = trans[sym] || '—';
      html += `<td style="padding:8px;border-bottom:1px solid #f1f5f9;">${esc(to)}</td>`;
    });

    html += `<td style="padding:8px;border-bottom:1px solid #f1f5f9;">${isAcc ? '✅' : ''}</td>`;
    html += '</tr>';
  });

  html += '</tbody></table>';
  return html;
}

/* Render full pipeline summary */
function renderNfaToMinDfa(text) {
  const nfa = parseNFACombined(text);
  if (nfa.error) {
    return `<div style="color:#b91c1c;font-weight:bold;">Error: ${escapeHtml(nfa.error)}</div>`;
  }

  const dfa = nfaToDfaCombined(nfa);
  if (dfa.error) return renderDfaTableCombined(dfa);

  const dfaCompleted = completeDFACombined(dfa);
  const dfaMin = minimizeDFACombined(dfaCompleted);

  const esc = escapeHtml;

  let html = `<div style="font-family:monospace;font-size:13px;margin-bottom:12px;">
    <div><strong>NFA states:</strong> ${esc(nfa.states.join(', '))}</div>
    <div><strong>Alphabet:</strong> ${esc((nfa.alphabet || []).join(', ') || '∅')}</div>
    <div><strong>Start:</strong> ${esc(nfa.start)}</div>
    <div><strong>Accepting:</strong> ${esc((nfa.accepts || []).join(', ') || '∅')}</div>
  </div>`;

  html += `<h4 style="margin:6px 0;">Completed DFA</h4>`;
  html += renderDfaTableCombined(dfaCompleted);

  html += `<h4 style="margin:16px 0 6px;">Minimized DFA</h4>`;
  html += renderDfaTableCombined(dfaMin);

  return html;
}

/* Hook up the NFA → Min DFA tab */
document.addEventListener('DOMContentLoaded', () => {
  const get = id => document.getElementById(id);

  const btnEx = get('example-nfa-dfa');
  if (btnEx) {
    btnEx.addEventListener('click', () => {
      const el = get('nfa-input');
      if (el) {
        el.value =
`States: q0,q1,q2
Alphabet: a,b
Start: q0
Accept: q2
Transitions:
q0,a->q0
q0,b->q1
q1,b->q2`;
      }
      toast('Example Loaded');
    });
  }

  const btnRun = get('run-nfa-dfa');
  if (btnRun) {
    btnRun.addEventListener('click', () => {
      const el = get('nfa-input');
      const out = get('nfa-dfa-output');
      if (!el || !out) return;
      const raw = el.value.trim();
      if (!raw) return toast('Please enter an NFA description');
      out.innerHTML = renderNfaToMinDfa(raw);
    });
  }
});


