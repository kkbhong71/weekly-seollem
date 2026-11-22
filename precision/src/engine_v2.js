/* =========================================================================
   PRECISION ENGINE v2.0 (JavaScript 이식판)
   원본: lotto_integrated_v2_0.py — v1.2 원본 조합 점수 방식 (인기도 미사용)
   ─────────────────────────────────────────────────────────────────────────
   [구성]
     ① 수학 상수 · 난수(시드 고정 가능)
     ② CSV 안전 로더 (회차 정렬 · 보너스 분리 · CP949)
     ③ DataEngine  : 8종 번호 점수 (빈도·최근·갭·쌍·모멘텀·구간·마르코프·Lift)
     ④ 특징 22종 + KMeans(실루엣 최적 K) 클러스터
     ⑤ FilterSystem: 12종 필터
     ⑥ EnsembleGenerator: 4종 생성 + v1.2 조합 점수 + 커버리지·클러스터 다양성 선택
     ⑦ 검증: 랜덤 대조군(회차별 짝지은 비교) · 부트스트랩 · 이항검정 · 다중 윈도우
   [원칙] Python 원본과 같은 수식·같은 연산 순서로 작성 → 점수는 Python과 교차검증
   ========================================================================= */
const PRECISION = (() => {
  'use strict';

  /* ---------- ① 상수: 로또 6/45의 수학적 사실 ---------- */
  const comb = (n, k) => { let r = 1; for (let i = 1; i <= k; i++) r = r * (n - k + i) / i; return Math.round(r); };
  const TOTAL = comb(45, 6);                                            // 8,145,060
  const MATCH_PMF = [0, 1, 2, 3, 4, 5, 6].map(k => comb(6, k) * comb(39, 6 - k) / TOTAL);
  const THEORY_MEAN = 0.8;
  const THEORY_VAR = 6 * (6 / 45) * (1 - 6 / 45) * (39 / 44);
  const P_GE3 = MATCH_PMF[3] + MATCH_PMF[4] + MATCH_PMF[5] + MATCH_PMF[6];
  const PRIMES = new Set([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]);

  const DEFAULT_CONFIG = {
    SUM_RANGE: [95, 200], SUM_OPTIMAL: [110, 190], MIN_AC: 7,
    ODD_RATES: [2, 3, 4], HIGH_RATES: [2, 3, 4], MIN_ZONES: 3, MAX_PER_ZONE: 3,
    MIN_UNIQUE_ENDINGS: 3, MAX_SAME_ENDING: 2, PRIME_RANGE: [1, 4],
    MAX_CONSECUTIVE: 2, PREV_MATCH_RANGE: [0, 3],
    W: { frequency: 0.15, recency: 0.15, gap: 0.13, pair: 0.12, momentum: 0.16, zone: 0.11, markov: 0.10, assoc: 0.08 },
    MARKOV_ALPHA: 1.0, MARKOV_DECAY: 0.999, ASSOC_WINDOW: 300, ASSOC_SHRINK: 2.0,
    RECENT_PERIODS: [10, 30, 50, 100], N_CLUSTERS: 5, MAX_SET_OVERLAP: 1,
    // v1.2 원본 조합 점수 가중치 (합계 1.00)
    SCORE_W: { sum: 0.12, ac: 0.12, num: 0.28, pair: 0.18, balance: 0.13, cluster: 0.10, algo: 0.07 },
  };

  /* 시드 고정 난수 (sfc32). 같은 시드 = 같은 결과 → 재현 가능 */
  class Rng {
    constructor(seed) {
      let s = (seed >>> 0) || 1;
      const sm = () => { s = (s + 0x9E3779B9) >>> 0; let z = s; z = Math.imul(z ^ (z >>> 16), 0x85EBCA6B); z = Math.imul(z ^ (z >>> 13), 0xC2B2AE35); return (z ^ (z >>> 16)) >>> 0; };
      this.a = sm(); this.b = sm(); this.c = sm(); this.d = sm();
      for (let i = 0; i < 12; i++) this.next();
    }
    next() {
      const t = (((this.a + this.b) >>> 0) + this.d) >>> 0;
      this.d = (this.d + 1) >>> 0; this.a = this.b ^ (this.b >>> 9);
      this.b = (this.c + (this.c << 3)) >>> 0; this.c = ((this.c << 21) | (this.c >>> 11)) >>> 0;
      this.c = (this.c + t) >>> 0; return t;
    }
    random() { return this.next() / 4294967296; }
    int(lo, hi) { return lo + Math.floor(this.random() * (hi - lo)); }       // [lo, hi)
    // 가중치 비복원 추출: 한 개 뽑을 때마다 남은 가중치로 다시 정규화 (numpy choice와 같은 방식)
    choice(items, k, w) {
      const it = items.slice(), ww = w ? w.slice() : items.map(() => 1), out = [];
      for (let j = 0; j < k; j++) {
        let tot = 0; for (const x of ww) tot += x;
        if (!(tot > 0)) return null;
        let r = this.random() * tot, i = 0;
        for (; i < ww.length - 1; i++) { r -= ww[i]; if (r < 0) break; }
        out.push(it[i]); it.splice(i, 1); ww.splice(i, 1);
      }
      return out;
    }
  }
  const randomSeed = () => { try { const a = new Uint32Array(1); crypto.getRandomValues(a); return a[0]; } catch (e) { return (Math.random() * 2 ** 32) >>> 0; } };

  /* ---------- 작은 수학 도구 (numpy와 같은 정의) ---------- */
  const sortNum = a => a.slice().sort((x, y) => x - y);
  function percentile(arr, q) {               // numpy 기본(linear) 보간
    const s = sortNum(arr), pos = (s.length - 1) * q / 100, lo = Math.floor(pos), hi = Math.ceil(pos);
    return s[lo] + (s[hi] - s[lo]) * (pos - lo);
  }
  const median = a => percentile(a, 50);
  const mean = a => a.reduce((x, y) => x + y, 0) / a.length;
  const varp = a => { const m = mean(a); return a.reduce((s, x) => s + (x - m) * (x - m), 0) / a.length; };
  const clip = (x, lo, hi) => Math.min(hi, Math.max(lo, x));

  /* =======================================================================
     ② CSV 안전 로더 — Python load_lotto_csv와 같은 판단 순서
     인코딩 → 유령 열 제거 → 회차·날짜·보너스 열 식별 → 번호 6열(이름 → 보너스 앞 6열 →
     후보 6열 → 오름차순 블록) → 규칙 검증 → 회차(또는 날짜) 오름차순 정렬 · 중복 제거
     ======================================================================= */
  function decodeBytes(buf) {
    try { return new TextDecoder('utf-8', { fatal: true }).decode(buf); } catch (e) { return new TextDecoder('euc-kr').decode(buf); }
  }
  const normCol = c => String(c).replace(/[\s_\-.()"]/g, '').toLowerCase();
  const EXCL = ['당첨자', '당첨금', '금액', '자수', 'winner', 'prize', 'amount', '상금', '판매', 'sales', '년도', 'year'];
  const BONUS = ['보너스', 'bonus', 'bnus', 'bns'], DATE = ['날짜', '일자', '추첨일', 'date'];
  const ROUND_EXACT = new Set(['회차', '회', 'round', 'drwno', 'drawno', 'turn', 'no', 'draw', 'rnd']);
  const NUM_RE = /^(?:num|number|no|번호|당첨번호|drwtno|ball|n|b)?([1-6])(?:번|번째)?$/;

  function splitLine(line, d) {               // 따옴표 안 쉼표(금액 "1,234") 보호
    const out = []; let cur = '', q = false;
    for (const ch of line) { if (ch === '"') q = !q; else if (ch === d && !q) { out.push(cur); cur = ''; } else cur += ch; }
    out.push(cur); return out.map(s => s.trim());
  }
  const toNum = s => { const t = String(s ?? '').replace(/,/g, '').trim(); return t === '' || isNaN(+t) ? NaN : +t; };

  function parseCSV(text) {
    const lines = text.replace(/^﻿/, '').split(/\r?\n/).filter(l => l.trim());
    if (lines.length < 2) throw new Error('데이터 행이 없습니다.');
    const d = lines[0].includes('\t') ? '\t' : ',';
    let head = splitLine(lines[0], d), rows = lines.slice(1).map(l => splitLine(l, d));
    // 유령 열 제거 (줄 끝 쉼표로 생긴 빈 열)
    const keep = head.map((_, j) => rows.some(r => (r[j] ?? '').trim() !== ''));
    head = head.filter((_, j) => keep[j]); rows = rows.map(r => r.filter((_, j) => keep[j]));
    const nc = head.map(normCol), J = head.map((_, j) => j);
    const col = j => rows.map(r => r[j]);
    const lottoLike = j => { const v = col(j).map(toNum).filter(x => !isNaN(x)); if (!v.length) return false;
      return v.filter(x => x >= 1 && x <= 45 && Number.isInteger(x)).length / v.length >= 0.95; };
    let bonusJ = J.find(j => BONUS.some(k => nc[j].includes(k)));
    const dateJ = J.find(j => DATE.some(k => nc[j].includes(k)));
    const roundJ = J.find(j => j !== bonusJ && j !== dateJ && (ROUND_EXACT.has(nc[j]) || nc[j].includes('회차')));
    const special = new Set([bonusJ, dateJ, roundJ]);
    let numJ = null, method = '';
    const named = {};
    for (const j of J) { if (special.has(j)) continue; const m = nc[j].match(NUM_RE); if (m && !(m[1] in named)) named[m[1]] = j; }
    if (Object.keys(named).length === 6 && [1, 2, 3, 4, 5, 6].every(i => lottoLike(named[i]))) { numJ = [1, 2, 3, 4, 5, 6].map(i => named[i]); method = '열 이름'; }
    if (!numJ) {
      const cands = J.filter(j => !special.has(j) && !EXCL.some(k => nc[j].includes(k)) && lottoLike(j));
      if (bonusJ !== undefined) { const b = cands.filter(j => j < bonusJ); if (b.length >= 6) { numJ = b.slice(-6); method = '보너스 앞 6열'; } }
      if (!numJ && cands.length === 6) { numJ = cands; method = '번호 후보 6열'; }
      if (!numJ && cands.length > 6) {
        let best = -1, bs = 0;
        for (let s = 0; s + 6 <= cands.length; s++) {
          const blk = cands.slice(s, s + 6); let inc = 0;
          for (const r of rows) { const v = blk.map(j => toNum(r[j])); if (v.every((x, i) => i === 0 || x > v[i - 1])) inc++; }
          if (inc / rows.length > best) { best = inc / rows.length; bs = s; }
        }
        if (best >= 0.9) { numJ = cands.slice(bs, bs + 6); method = `오름차순 블록(${Math.round(best * 100)}%)`;
          if (bonusJ === undefined && bs + 6 < cands.length) bonusJ = cands[bs + 6]; }
        else { numJ = cands.slice(-6); method = '뒤 6열(추정)'; }
      }
      if (!numJ) throw new Error('번호 6개 열을 찾지 못했습니다.');
    }
    let recs = [], bad = 0;
    rows.forEach((r, i) => {
      const nums = numJ.map(j => toNum(r[j]));
      if (nums.some(x => !Number.isInteger(x) || x < 1 || x > 45) || new Set(nums).size !== 6) { bad++; return; }
      let round = roundJ !== undefined ? toNum(r[roundJ]) : NaN;
      if (roundJ !== undefined && isNaN(round)) { const m = String(r[roundJ]).match(/\d+/); round = m ? +m[0] : NaN; }
      const b = bonusJ !== undefined ? toNum(r[bonusJ]) : NaN;
      recs.push({ i, round, date: dateJ !== undefined ? r[dateJ] : '', nums: sortNum(nums),
        bonus: Number.isInteger(b) && b >= 1 && b <= 45 && !nums.includes(b) ? b : null });
    });
    let order = '파일 순서', flipped = false;
    if (roundJ !== undefined) {
      recs = recs.filter(x => !isNaN(x.round)); order = '회차';
      flipped = recs.length > 1 && recs[0].round > recs[recs.length - 1].round;
      recs.sort((a, b) => a.round - b.round || a.i - b.i);
      const m = new Map(); for (const x of recs) m.set(x.round, x); recs = [...m.values()];
    } else if (dateJ !== undefined) {
      const t = s => Date.parse(String(s).replace(/\./g, '-')); order = '날짜';
      recs = recs.filter(x => !isNaN(t(x.date)));
      flipped = recs.length > 1 && t(recs[0].date) > t(recs[recs.length - 1].date);
      recs.sort((a, b) => t(a.date) - t(b.date)); recs.forEach((x, k) => x.round = k + 1);
    } else recs.forEach((x, k) => x.round = k + 1);
    if (!recs.length) throw new Error('유효한 회차가 0건입니다.');
    const rounds = recs.map(x => x.round);
    const missing = order === '회차' ? (rounds[rounds.length - 1] - rounds[0] + 1) - rounds.length : 0;
    return { history: recs.map(x => x.nums), rounds, bonus: recs.map(x => x.bonus), dates: recs.map(x => x.date),
      info: { method, order, flipped, missing, bad, numCols: numJ.map(j => head[j]), bonusCol: bonusJ !== undefined ? head[bonusJ] : null } };
  }

  /* =======================================================================
     ③ DataEngine — 8종 번호 점수. 각 점수는 0~1로 정규화 후 가중합 → 합계 1로 정규화
     ======================================================================= */
  // 중앙값/IQR 기반 정규화: 극단값에 덜 흔들림. 인덱스 0(번호 0)은 계산에서 제외
  function robustNormalize(arr) {
    const s = arr.slice(1), out = arr.slice();
    const mx = Math.max(...s), mn = Math.min(...s);
    let norm;
    if (mx === mn) norm = s.map(() => 0.5);
    else {
      const med = median(s), iqr = percentile(s, 75) - percentile(s, 25);
      norm = iqr > 0 ? s.map(x => (clip((x - med) / iqr, -2, 2) + 2) / 4) : s.map(x => (x - mn) / (mx - mn));
    }
    for (let i = 0; i < 45; i++) out[i + 1] = norm[i];
    return out;
  }
  const zeros = n => new Array(n).fill(0);
  function countLast(H, p) { const c = zeros(46); for (const r of H.slice(-p)) for (const n of r) c[n]++; return c; }

  function analyze(history, config) {
    const cfg = config || DEFAULT_CONFIG, H = history, T = H.length;
    if (!T) throw new Error('분석할 회차가 없습니다.');
    const last = H[T - 1];

    // (1) 가중 빈도: 최근 10/30/50/100회 출현 횟수를 기대값(p·6/45)으로 나눠 기간별 가중
    const PW = { 10: 4.0, 30: 2.5, 50: 1.5, 100: 1.0 }, byPeriod = {};
    for (const p of cfg.RECENT_PERIODS) if (p <= T) byPeriod[p] = countLast(H, p);
    const wf = zeros(46);
    for (const p of [10, 30, 50, 100]) if (byPeriod[p]) for (let n = 0; n < 46; n++) wf[n] += byPeriod[p][n] / (p * 6 / 45) * PW[p];
    wf[0] = 0;
    const freq = robustNormalize(wf);
    const total = countLast(H, T);

    // (2) 갭: 현재 미출현 간격 / 평균 간격 비율이 0.8~1.5면 '나올 때가 된' 번호로 가산
    const gapRaw = zeros(46), gapNow = zeros(46), gapAvg = zeros(46);
    const pos = Array.from({ length: 46 }, () => []);
    H.forEach((r, i) => r.forEach(n => pos[n].push(i)));
    for (let n = 1; n <= 45; n++) {
      const idx = pos[n];
      if (idx.length > 1) {
        let sd = 0; for (let k = 1; k < idx.length; k++) sd += idx[k] - idx[k - 1];
        const avg = sd / (idx.length - 1), gap = T - 1 - idx[idx.length - 1];
        gapAvg[n] = avg; gapNow[n] = gap;
        const ratio = avg > 0 ? gap / avg : 1;
        gapRaw[n] = ratio >= 0.8 && ratio <= 1.5 ? 1.0 - Math.abs(ratio - 1.0) * 0.3
          : ratio > 1.5 ? Math.max(0.15, 1.0 - (ratio - 1.5) * 0.2) : Math.max(0.25, ratio * 0.6);
      } else { gapRaw[n] = 0.3; gapNow[n] = T; gapAvg[n] = T / 2; }
    }
    const gap = robustNormalize(gapRaw);

    // (3) 쌍(동반출현): 최근 100회에서 같이 나온 횟수 / 100
    const pw = Math.min(100, T), co = Array.from({ length: 46 }, () => zeros(46));
    for (const r of H.slice(-pw)) for (let i = 0; i < 6; i++) for (let j = 0; j < 6; j++) if (i !== j) co[r[i]][r[j]]++;
    const pairScore = co.map(row => row.map(v => v / pw));
    const strength = pairScore.map(row => row.reduce((s, v) => s + v, 0));
    const pairStrength = robustNormalize(strength);
    const tri = [];
    for (let a = 0; a < 46; a++) for (let b = a + 1; b < 46; b++) tri.push([a, b, co[a][b]]);
    const topPairs = tri.map((x, k) => [x, k]).sort((p, q) => q[0][2] - p[0][2] || p[1] - q[1])
      .slice(0, 50).filter(p => p[0][2] > 0).map(p => [[p[0][0], p[0][1]], p[0][2]]);

    // (4) 모멘텀: 최근 10회 출현률 / 최근 30회 출현률
    const momRaw = zeros(46), trend = {};
    if (T >= 30) {
      const s10 = countLast(H, 10), s30 = countLast(H, 30);
      for (let n = 1; n <= 45; n++) {
        const sh = s10[n] / 10, mid = s30[n] / 30;
        if (mid > 0) { const m = sh / mid; momRaw[n] = m; trend[n] = m > 1.3 ? 'UP' : m < 0.7 ? 'DOWN' : 'STABLE'; }
        else { momRaw[n] = sh > 0 ? 1.0 : 0.5; trend[n] = sh > 0 ? 'UP' : 'DORMANT'; }
      }
    }
    const momentum = robustNormalize(momRaw);

    // (5) 구간: 최근 50회, 같은 번호대 안에서 최다 출현 번호 대비 비율
    const c50 = countLast(H, 50), zoneScore = zeros(46);
    for (const [zs, ze] of [[1, 10], [11, 20], [21, 30], [31, 40], [41, 45]]) {
      let mx = 0; for (let n = zs; n <= ze; n++) mx = Math.max(mx, c50[n]);
      for (let n = zs; n <= ze; n++) zoneScore[n] = mx > 0 ? c50[n] / mx : 0;
    }

    // (6) 마르코프: P(n이 이번 회차 | m이 직전 회차), 오래된 전이는 0.999^거리로 감쇠, 라플라스 평활
    const trans = Array.from({ length: 46 }, () => zeros(46));
    for (let t = 1; t < T; t++) {
      const w = Math.pow(cfg.MARKOV_DECAY, T - 1 - t);
      for (const m of H[t - 1]) for (const n of H[t]) trans[m][n] += w;
    }
    const prob = Array.from({ length: 46 }, () => zeros(46));
    for (let m = 1; m <= 45; m++) {
      let rs = 0; for (let n = 1; n <= 45; n++) rs += trans[m][n];
      for (let n = 1; n <= 45; n++) prob[m][n] = (trans[m][n] + cfg.MARKOV_ALPHA) / (rs + cfg.MARKOV_ALPHA * 45);
    }
    const mkRaw = zeros(46);
    for (let n = 1; n <= 45; n++) { let s = 0; for (const m of last) s += prob[m][n]; mkRaw[n] = s / last.length; }
    const markov = robustNormalize(mkRaw);

    // (7) Lift 연관규칙: 관측 동반횟수 / 기대 동반횟수 (6개 비복원 보정), 표본이 적으면 1 쪽으로 수축
    const W = Math.min(cfg.ASSOC_WINDOW, T), Hw = H.slice(-W), f = countLast(H, W);
    const r = f.map(x => (x + 6 / 45) / (W + 1));
    const coW = Array.from({ length: 46 }, () => zeros(46));
    for (const rr of Hw) for (const a of rr) for (const b of rr) coW[a][b]++;     // 대각 포함 (Python Xw.T@Xw)
    const lift = Array.from({ length: 46 }, () => zeros(46)), m0 = cfg.ASSOC_SHRINK;
    for (let a = 0; a < 46; a++) for (let b = 0; b < 46; b++) {
      if (a === 0 || b === 0 || a === b) { lift[a][b] = 1; continue; }
      const E = W * (r[a] * r[b]) * (5 / 44) / (6 / 45);
      lift[a][b] = (coW[a][b] + m0) / (E + m0);
    }
    const acRaw = new Array(46).fill(1);
    for (let n = 1; n <= 45; n++) { const o = last.filter(x => x !== n); acRaw[n] = o.length ? o.reduce((s, x) => s + lift[n][x], 0) / o.length : 1; }
    const assoc = robustNormalize(acRaw);
    const rules = [];
    for (let a = 1; a < 46; a++) for (let b = a + 1; b < 46; b++) if (coW[a][b] >= 2) rules.push([a, b, lift[a][b]]);
    const topRules = rules.map((x, k) => [x, k]).sort((p, q) => q[0][2] - p[0][2] || p[1] - q[1]).slice(0, 15).map(p => p[0]);

    // 최종 점수: 8종 가중합 → 합계 1 정규화 (생성 단계의 추출 확률로 사용)
    const c10 = countLast(H, 10), Wt = cfg.W, fin = zeros(46);
    for (let n = 0; n < 46; n++) {
      const rec = Math.min(c10[n] / (10 * 6 / 45), 1.5) / 1.5;
      fin[n] = freq[n] * Wt.frequency + rec * Wt.recency + gap[n] * Wt.gap + pairStrength[n] * Wt.pair
        + momentum[n] * Wt.momentum + zoneScore[n] * Wt.zone + markov[n] * Wt.markov + assoc[n] * Wt.assoc;
    }
    fin[0] = 0;
    let fs = 0; for (let n = 1; n <= 45; n++) fs += fin[n];
    if (fs > 0) for (let n = 1; n <= 45; n++) fin[n] /= fs;

    return { T, last, history: H, config: cfg, total, byPeriod, freq, gap, gapNow, gapAvg, pairScore, pairStrength, topPairs,
      momentum, trend, zoneScore, markov, markovRaw: mkRaw, assoc, assocRaw: acRaw, lift, topRules, assocWindow: W,
      final: fin, historicalSets: new Set(H.map(x => x.join(','))) };
  }
  const hotNumbers = (E, n = 10) => [...Array(45).keys()].map(i => i + 1).sort((a, b) => E.final[b] - E.final[a] || a - b).slice(0, n);
  const coldNumbers = (E, n = 10) => [...Array(45).keys()].map(i => i + 1).sort((a, b) => E.final[a] - E.final[b] || a - b).slice(0, n);

  /* =======================================================================
     ④ 조합 특징 22종 + KMeans 클러스터
     당첨 조합들을 '모양'(합계·간격·구간 분포·홀짝 등)으로 묶어, 추천 세트가
     한 가지 모양에만 몰리지 않도록(클러스터 다양성) 하는 데 사용
     ======================================================================= */
  function features(c) {
    const a = sortNum(c), g = [1, 2, 3, 4, 5].map(i => a[i] - a[i - 1]);
    const zones = [0, 0, 0, 0, 0]; for (const n of a) zones[Math.min(Math.floor((n - 1) / 10), 4)]++;
    const d = new Set(); for (let i = 0; i < 6; i++) for (let j = i + 1; j < 6; j++) d.add(a[j] - a[i]);
    const m = mean(a), gm = mean(g);
    return [a.reduce((s, x) => s + x, 0), m, Math.sqrt(varp(a)), a[5] - a[0],
      gm, Math.sqrt(varp(g)), Math.max(...g), Math.min(...g), a[0], a[5], a[2] + a[3], ...zones,
      a.filter(x => x % 2 === 1).length, a.filter(x => x >= 23).length, d.size - 5,
      new Set(a.map(x => x % 10)).size, a.filter(x => PRIMES.has(x)).length, g.filter(x => x === 1).length];
  }
  const dist2 = (p, q) => { let s = 0; for (let i = 0; i < p.length; i++) { const t = p[i] - q[i]; s += t * t; } return s; };

  function kmeans(X, k, rng, nInit, maxIter = 300) {
    let best = null;
    for (let run = 0; run < nInit; run++) {
      // k-means++ 초기화: 멀리 떨어진 점일수록 다음 중심으로 뽑힐 확률 ↑
      const C = [X[rng.int(0, X.length)].slice()];
      const D = X.map(x => dist2(x, C[0]));
      while (C.length < k) {
        let tot = D.reduce((s, x) => s + x, 0), r = rng.random() * tot, i = 0;
        for (; i < X.length - 1; i++) { r -= D[i]; if (r < 0) break; }
        C.push(X[i].slice()); for (let j = 0; j < X.length; j++) D[j] = Math.min(D[j], dist2(X[j], C[C.length - 1]));
      }
      const lab = new Int32Array(X.length);
      for (let it = 0; it < maxIter; it++) {
        let moved = 0;
        for (let j = 0; j < X.length; j++) {
          let bi = 0, bd = Infinity; for (let c = 0; c < k; c++) { const dd = dist2(X[j], C[c]); if (dd < bd) { bd = dd; bi = c; } }
          if (lab[j] !== bi || it === 0) { if (lab[j] !== bi) moved++; lab[j] = bi; }
        }
        const sum = Array.from({ length: k }, () => zeros(X[0].length)), cnt = zeros(k);
        for (let j = 0; j < X.length; j++) { cnt[lab[j]]++; const s = sum[lab[j]]; for (let f = 0; f < s.length; f++) s[f] += X[j][f]; }
        for (let c = 0; c < k; c++) if (cnt[c]) C[c] = sum[c].map(v => v / cnt[c]);
        if (it > 0 && moved === 0) break;
      }
      let inertia = 0; for (let j = 0; j < X.length; j++) inertia += dist2(X[j], C[lab[j]]);
      if (!best || inertia < best.inertia) best = { C, lab: Array.from(lab), inertia };
    }
    return best;
  }
  // 실루엣 점수: 같은 묶음과 가깝고 다른 묶음과 멀수록 1에 가까움 (거리 행렬은 한 번만 계산해 재사용)
  function silhouette(Dm, lab, k) {
    const n = lab.length; let tot = 0;
    for (let i = 0; i < n; i++) {
      const s = zeros(k), c = zeros(k);
      for (let j = 0; j < n; j++) if (j !== i) { s[lab[j]] += Dm[i * n + j]; c[lab[j]]++; }
      const a = c[lab[i]] ? s[lab[i]] / c[lab[i]] : 0;
      let b = Infinity; for (let q = 0; q < k; q++) if (q !== lab[i] && c[q]) b = Math.min(b, s[q] / c[q]);
      tot += c[lab[i]] && isFinite(b) ? (b - a) / Math.max(a, b) : 0;
    }
    return tot / n;
  }

  function buildClusters(E, nClusters, fast, seed) {
    const H = E.history, rng = new Rng(seed ^ 0x5bd1e995);
    const G = { nClusters, stats: {}, top: [], kind: 'simple' };
    if (H.length > 30) {
      const F = H.map(features), dim = F[0].length;
      const mu = zeros(dim), sd = zeros(dim);
      for (const x of F) for (let i = 0; i < dim; i++) mu[i] += x[i] / F.length;
      for (const x of F) for (let i = 0; i < dim; i++) sd[i] += (x[i] - mu[i]) ** 2 / F.length;
      for (let i = 0; i < dim; i++) sd[i] = Math.sqrt(sd[i]) || 1;
      const scale = x => x.map((v, i) => (v - mu[i]) / sd[i]);
      const X = F.map(scale);
      let bestK = Math.min(nClusters, Math.max(2, Math.floor(H.length / 15))), nInit = 3;
      if (!fast) {
        nInit = 5; let bestS = -1; const n = X.length, Dm = new Float64Array(n * n);
        for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) { const d = Math.sqrt(dist2(X[i], X[j])); Dm[i * n + j] = d; Dm[j * n + i] = d; }
        const maxK = Math.max(3, Math.min(10, Math.floor(n / 15)));
        for (let k = 3; k <= maxK; k++) {
          const km = kmeans(X, k, rng, nInit); if (new Set(km.lab).size < 2) continue;
          const s = silhouette(Dm, km.lab, k); if (s > bestS) { bestS = s; bestK = k; }
        }
        G.silhouette = bestS;
      }
      const km = kmeans(X, bestK, rng, nInit);
      Object.assign(G, { kind: 'kmeans', nClusters: bestK, centers: km.C, labels: km.lab, scale });
      G.idOf = c => { const x = scale(features(c)); let bi = 0, bd = Infinity; km.C.forEach((cc, i) => { const d = dist2(x, cc); if (d < bd) { bd = d; bi = i; } }); return bi; };
    } else {
      const sums = H.map(r => r.reduce((s, x) => s + x, 0)), q33 = percentile(sums, 33), q66 = percentile(sums, 66);
      const dig = s => s < q33 ? 0 : s < q66 ? 1 : 2;
      Object.assign(G, { nClusters: 3, labels: sums.map(dig) });
      G.idOf = c => dig(c.reduce((s, x) => s + x, 0));
    }
    const rn = Math.min(50, H.length), rec = G.labels.slice(-rn);
    for (let c = 0; c < G.nClusters; c++) {
      const idx = G.labels.map((l, i) => l === c ? i : -1).filter(i => i >= 0);
      G.stats[c] = { count: idx.length, ratio: idx.length / H.length,
        avgSum: idx.length ? mean(idx.map(i => H[i].reduce((s, x) => s + x, 0))) : 0,
        avgSpread: idx.length ? mean(idx.map(i => H[i][5] - H[i][0])) : 0,
        recentRatio: rec.filter(l => l === c).length / rn };
    }
    G.top = Object.keys(G.stats).map(Number).filter(c => G.stats[c].count > 0)
      .map(c => [c, G.stats[c].ratio * 0.5 + G.stats[c].recentRatio * 0.5]).sort((a, b) => b[1] - a[1] || a[0] - b[0])
      .slice(0, 3).map(x => x[0]);
    G.bonusOf = c => c === G.top[0] ? 1.0 : G.top.slice(1).includes(c) ? 0.6 : 0.2;
    return G;
  }

  /* =======================================================================
     ⑤ FilterSystem — 12종 필터 (Python과 같은 순서로 검사, 처음 걸린 필터로 기록)
     ======================================================================= */
  function makeFilter(E) {
    const cfg = E.config, lastSet = new Set(E.last);
    const checks = [
      ['합계', n => { const s = n.reduce((a, b) => a + b, 0); return s >= cfg.SUM_RANGE[0] && s <= cfg.SUM_RANGE[1]; }],
      ['AC값', n => { const d = new Set(); for (let i = 0; i < 6; i++) for (let j = i + 1; j < 6; j++) d.add(n[j] - n[i]); return d.size - 5 >= cfg.MIN_AC; }],
      ['홀짝', n => cfg.ODD_RATES.includes(n.filter(x => x & 1).length)],
      ['고저', n => cfg.HIGH_RATES.includes(n.filter(x => x >= 23).length)],
      ['구간', n => { const z = zeros(5); n.forEach(x => z[Math.min(Math.floor((x - 1) / 10), 4)]++); return z.filter(c => c > 0).length >= cfg.MIN_ZONES && Math.max(...z) <= cfg.MAX_PER_ZONE; }],
      ['연속', n => { let run = 1; for (let i = 0; i < 5; i++) { run = n[i + 1] === n[i] + 1 ? run + 1 : 1; if (run > cfg.MAX_CONSECUTIVE) return false; } return true; }],
      ['끝수', n => { const e = {}; n.forEach(x => e[x % 10] = (e[x % 10] || 0) + 1); const v = Object.values(e); return v.length >= cfg.MIN_UNIQUE_ENDINGS && Math.max(...v) <= cfg.MAX_SAME_ENDING; }],
      ['소수', n => { const p = n.filter(x => PRIMES.has(x)).length; return p >= cfg.PRIME_RANGE[0] && p <= cfg.PRIME_RANGE[1]; }],
      ['이전회차', n => { const m = n.filter(x => lastSet.has(x)).length; return m >= cfg.PREV_MATCH_RANGE[0] && m <= cfg.PREV_MATCH_RANGE[1]; }],
      ['역대중복', n => !E.historicalSets.has(n.join(','))],
      ['간격', n => { const g = (n[5] - n[0]) / 5; return g >= 3.5 && g <= 13.0; }],
      ['경계', n => !(n.includes(1) && n.includes(45)) || n.some(x => x >= 18 && x <= 27)],
    ];
    const F = { checked: 0, passed: 0, rej: {} };
    F.reset = () => { F.checked = 0; F.passed = 0; F.rej = {}; };
    F.apply = (nums, track = true) => {
      const n = sortNum(nums); if (track) F.checked++;
      for (const [name, fn] of checks) if (!fn(n)) { if (track) F.rej[name] = (F.rej[name] || 0) + 1; return [false, name]; }
      if (track) F.passed++; return [true, ''];
    };
    return F;
  }

  /* =======================================================================
     ⑥ EnsembleGenerator — 4종 생성 → v1.2 조합 점수 → 커버리지·클러스터 다양성 선택
     ======================================================================= */
  const BALLS = [...Array(45).keys()].map(i => i + 1);
  const ZONES = [[1, 10], [11, 20], [21, 30], [31, 40], [41, 45]];

  function generate(E, G, rng, count = 5) {
    const cfg = E.config, F = makeFilter(E), w = BALLS.map(n => Math.max(E.final[n], 1e-12));
    const seen = new Set(); let attempts = 0, passedN = 0;
    const tryAdd = (nums, algo, res) => {
      attempts++; const n = sortNum(nums), key = n.join(',');
      if (F.apply(n)[0] && !seen.has(key)) { seen.add(key); passedN++; res.push({ nums: n, algo }); }
    };
    const per = Math.max(count * 6, 30);
    // 알고리즘 1 — 가중치: 최종 점수에 비례해 6개 추출
    const weighted = k => { const res = []; for (let i = 0; i < k * 40 && res.length < k; i++) { const x = rng.choice(BALLS, 6, w); if (x) tryAdd(x, 'weighted', res); } return res; };
    // 알고리즘 2 — 구간 밸런스: 5개 번호대에서 1개씩 + 한 구간에서 1개 더
    const balanced = k => { const res = []; for (let i = 0; i < k * 40 && res.length < k; i++) {
      const picks = [1, 1, 1, 1, 1]; picks[rng.int(0, 5)]++; const nums = [];
      ZONES.forEach(([zs, ze], z) => { const it = BALLS.slice(zs - 1, ze), ww = w.slice(zs - 1, ze); nums.push(...rng.choice(it, picks[z], ww)); });
      tryAdd(nums, 'balanced', res); } return res; };
    // 알고리즘 3 — 동반출현: 70% 확률로 상위 15개 쌍 중 하나에서 출발
    const pattern = k => { const res = [], top = E.topPairs.slice(0, 15);
      for (let i = 0; i < k * 40 && res.length < k; i++) {
        const base = top.length && rng.random() < 0.7 ? top[rng.int(0, top.length)][0].slice() : [];
        const ww = w.map((v, j) => base.includes(j + 1) ? 0 : v), extra = rng.choice(BALLS, 6 - base.length, ww);
        if (extra) tryAdd(base.concat(extra), 'pattern', res); } return res; };
    // 알고리즘 4 — 다중 클러스터: 상위 클러스터의 평균 폭으로 양 끝을 정하고, 그 사이에서 4개
    const multiCluster = k => { const res = [], st = G.stats, tg = G.top;
      for (let i = 0; i < k * 50 && res.length < k; i++) {
        const cid = tg[rng.int(0, tg.length)];
        const spread = clip(Math.trunc(st[cid].avgSpread + rng.int(-5, 6)), 18, 44);
        const first = rng.int(1, 46 - spread), lastN = first + spread;
        const inner = BALLS.filter(n => n > first && n < lastN), mids = rng.choice(inner, 4, inner.map(n => w[n - 1]));
        const nums = [first, lastN, ...mids];
        if (Math.abs(nums.reduce((s, x) => s + x, 0) - st[cid].avgSum) <= 35) tryAdd(nums, 'cluster_' + cid, res);
      } return res; };

    const plan = [['Weighted', weighted], ['Balanced', balanced], ['Pattern', pattern]];
    if (G && G.top.length) plan.push(['MultiCluster', multiCluster]);
    const perAlgo = [], cands = [];
    for (const [name, fn] of plan) { const c = fn(per); perAlgo.push([name, c.length]); cands.push(...c); }

    // ── v1.2 조합 점수 ──
    let mxNum = 0, mxPair = 0;
    for (const c of cands) {
      c.numRaw = c.nums.reduce((s, n) => s + E.final[n], 0);
      let p = 0; for (let i = 0; i < 6; i++) for (let j = i + 1; j < 6; j++) p += E.pairScore[c.nums[i]][c.nums[j]];
      c.pairRaw = p; mxNum = Math.max(mxNum, c.numRaw); mxPair = Math.max(mxPair, p);
    }
    mxNum = mxNum > 0 ? mxNum : 1; mxPair = mxPair > 0 ? mxPair : 1;
    const SW = cfg.SCORE_W, [lo, hi] = cfg.SUM_OPTIMAL;
    for (const c of cands) {
      const ft = features(c.nums), s = ft[0], ac = ft[18], cid = G ? G.idOf(c.nums) : -1, cb = G ? G.bonusOf(cid) : 0.5;
      const parts = { sum: s >= lo && s <= hi ? 1.0 : 0.5, ac: clip(ac / 10, 0, 1), num: c.numRaw / mxNum, pair: c.pairRaw / mxPair,
        balance: 1 / (1 + varp(ft.slice(11, 16))), cluster: cb, algo: c.algo === 'balanced' ? 1.0 : 0.8 };
      c.stat = { sum: s, ac, odd: ft[16], high: ft[17], prime: ft[20], clusterId: cid, clusterBonus: cb, parts };
      c.score = Math.round(Object.keys(parts).reduce((t, k) => t + parts[k] * SW[k], 0) * 1e6) / 1e6;
    }

    // ── 클러스터 쿼터 풀: 클러스터마다 상위 count개를 먼저 확보 → 나머지는 점수순 ──
    const ranked = cands.slice().sort((a, b) => b.score - a.score);
    const byC = new Map(); for (const c of ranked) { if (!byC.has(c.stat.clusterId)) byC.set(c.stat.clusterId, []); byC.get(c.stat.clusterId).push(c); }
    const pool = [], inPool = new Set();
    for (const list of byC.values()) for (const c of list.slice(0, count)) { pool.push(c); inPool.add(c); }
    for (const c of ranked) { if (pool.length >= Math.max(count * 10, 50)) break; if (!inPool.has(c)) { pool.push(c); inPool.add(c); } }

    // ── 선택: 점수 70% + 새 번호 커버리지 30%, 세트 간 중복 ≤1, 한 클러스터 최대 count/2 ──
    const sel = [], used = new Set(), cc = {}, maxCls = Math.max(1, Math.floor(count / 2)), maxOv = cfg.MAX_SET_OVERLAP;
    const ovOk = c => sel.every(s => c.nums.filter(x => s.nums.includes(x)).length <= maxOv);
    const pick = src => { let best = null, bv = -1;
      for (const c of src) { if (sel.includes(c) || !ovOk(c) || (cc[c.stat.clusterId] || 0) >= maxCls) continue;
        const v = c.score * 0.7 + c.nums.filter(x => !used.has(x)).length / 6 * 0.3; if (v > bv) { bv = v; best = c; } }
      return best; };
    for (let i = 0; i < count; i++) {
      let best = pick(pool) || pick(cands);            // 풀 → 전체 후보 순으로 클러스터 다양성 유지 시도
      if (!best) { const rest = pool.filter(c => !sel.includes(c) && ovOk(c)); const r2 = rest.length ? rest : pool.filter(c => !sel.includes(c));
        if (!r2.length) break; best = r2.reduce((a, b) => b.score > a.score ? b : a); }
      sel.push(best); best.nums.forEach(x => used.add(x)); cc[best.stat.clusterId] = (cc[best.stat.clusterId] || 0) + 1;
    }
    return { sets: sel, candidates: cands.length, perAlgo, attempts, passed: passedN, filter: F };
  }

  /* 한 번에 실행: 분석 → 클러스터 → 생성 */
  function run(history, opt = {}) {
    const cfg = opt.config || DEFAULT_CONFIG, seed = opt.seed ?? 42;
    const E = analyze(history, cfg), G = buildClusters(E, cfg.N_CLUSTERS, !!opt.fast, seed);
    const out = generate(E, G, new Rng(seed), opt.count || 5);
    return Object.assign(out, { E, G });
  }

  /* =======================================================================
     ⑦ 검증 도구
     ======================================================================= */
  function bootstrapCI(x, nBoot = 4000, seed = 0) {
    if (!x.length) return [0, 0];
    const rng = new Rng(seed + 1), means = new Float64Array(nBoot);
    for (let b = 0; b < nBoot; b++) { let s = 0; for (let i = 0; i < x.length; i++) s += x[rng.int(0, x.length)]; means[b] = s / x.length; }
    const arr = Array.from(means); return [percentile(arr, 2.5), percentile(arr, 97.5)];
  }
  function lgamma(z) {                             // Lanczos 근사 (이항검정 로그 계산용)
    const g = 7, c = [0.99999999999980993, 676.5203681218851, -1259.1392167224028, 771.32342877765313, -176.61502916214059, 12.507343278686905, -0.13857109526572012, 9.9843695780195716e-6, 1.5056327351493116e-7];
    if (z < 0.5) return Math.log(Math.PI / Math.sin(Math.PI * z)) - lgamma(1 - z);
    z -= 1; let x = c[0]; for (let i = 1; i < g + 2; i++) x += c[i] / (z + i);
    const t = z + g + 0.5; return 0.5 * Math.log(2 * Math.PI) + (z + 0.5) * Math.log(t) - t + Math.log(x);
  }
  function binomSF(k, n, p) {                     // P(X ≥ k), X ~ Binomial(n, p)
    if (k <= 0) return 1; if (k > n) return 0;
    const lp = Math.log(p), lq = Math.log1p(-p), terms = [];
    for (let i = k; i <= n; i++) terms.push(lgamma(n + 1) - lgamma(i + 1) - lgamma(n - i + 1) + i * lp + (n - i) * lq);
    const mx = Math.max(...terms); return Math.min(1, Math.exp(mx) * terms.reduce((s, t) => s + Math.exp(t - mx), 0));
  }
  const requiredSample = pct => { const d = THEORY_MEAN * pct / 100; return Math.ceil((1.959964 + 0.841621) ** 2 * THEORY_VAR / (d * d)); };

  // 랜덤 대조군 백테스트 1회차: 모델 / 순수 랜덤 / 필터 랜덤을 같은 회차에 동시 투입
  function backtestRound(H, idx, seedBase, cfg, nModel = 5, nCtrl = 100) {
    const prefix = H.slice(0, idx), actual = new Set(H[idx]);
    const r = run(prefix, { config: cfg, seed: (seedBase + idx) >>> 0, fast: true, count: nModel });
    const mm = r.sets.map(s => s.nums.filter(x => actual.has(x)).length);
    const rng = new Rng((seedBase * 7919 + idx) >>> 0);
    const pm = [], fm = []; const F = makeFilter(r.E);
    for (let i = 0; i < nCtrl; i++) pm.push(rng.choice(BALLS, 6).filter(x => actual.has(x)).length);
    for (let t = 0; fm.length < nCtrl && t < nCtrl * 200; t++) { const c = sortNum(rng.choice(BALLS, 6)); if (F.apply(c, false)[0]) fm.push(c.filter(x => actual.has(x)).length); }
    return { round: idx + 1, model: mm, pure: pm, filt: fm.length ? fm : pm, sets: r.sets.map(s => s.nums) };
  }
  function summarizeBacktest(rows, seed = 2026) {
    const M = rows.map(r => mean(r.model)), P = rows.map(r => mean(r.pure)), Fm = rows.map(r => mean(r.filt));
    const dP = M.map((x, i) => x - P[i]), dF = M.map((x, i) => x - Fm[i]);
    const ciP = bootstrapCI(dP, 4000, seed), ciF = bootstrapCI(dF, 4000, seed + 1);
    const verdict = ci => ci[0] <= 0 && 0 <= ci[1] ? '무작위와 구분 불가 (통계적 동등)' : ci[0] > 0 ? '무작위보다 우수' : '무작위보다 열등';
    const all = rows.flatMap(r => r.model), hits = all.filter(x => x >= 3).length;
    return { rounds: rows.length, modelAvg: mean(M), pureAvg: mean(P), filtAvg: mean(Fm), diffP: mean(dP), ciP, verdictP: verdict(ciP),
      diffF: mean(dF), ciF, verdictF: verdict(ciF), hits, n: all.length, hitsExp: all.length * P_GE3, pValue: binomSF(hits, all.length, P_GE3) };
  }

  // 다중 윈도우: 최근 30/50/100회/전체로 잘라 각각 예측 → 상위 번호가 얼마나 흔들리는지
  function multiWindow(H, seed = 42, count = 5, windows = [30, 50, 100, 0]) {
    const out = [];
    for (const w of windows) {
      const sub = w === 0 ? H : H.slice(-w); if (sub.length < 20) continue;
      const cfg = Object.assign({}, DEFAULT_CONFIG, { N_CLUSTERS: Math.min(5, Math.max(2, Math.floor(sub.length / 15))) });
      const r = run(sub, { config: cfg, seed, fast: true, count });
      out.push({ label: w === 0 ? '전체' : `최근 ${w}회`, rounds: sub.length, sets: r.sets.map(s => s.nums), top10: hotNumbers(r.E, 10) });
    }
    return out;
  }

  const prizeRank = (m, bonusHit) => m === 6 ? 1 : m === 5 ? (bonusHit ? 2 : 3) : m === 4 ? 4 : m === 3 ? 5 : 0;

  return { TOTAL, MATCH_PMF, THEORY_MEAN, THEORY_VAR, P_GE3, DEFAULT_CONFIG, Rng, randomSeed, decodeBytes, parseCSV,
    analyze, hotNumbers, coldNumbers, features, buildClusters, makeFilter, generate, run, bootstrapCI, binomSF,
    requiredSample, backtestRound, summarizeBacktest, multiWindow, prizeRank, percentile, mean };
})();
if (typeof module !== 'undefined') module.exports = PRECISION;
