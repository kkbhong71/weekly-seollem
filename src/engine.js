/* =========================================================
   ENGINE v0.2 — 화면과 무관한 순수 계산 모듈 (Node에서도 단독 테스트 가능)
   구성: ① 확률표 ② 진정 난수 생성기 ③ 데이터 분석 ④ 군중 선호(인기도) 모델
         ⑤ 균형 필터 ⑥ 렌즈 8종 생성기 ⑦ 유전 알고리즘 ⑧ walk-forward 백테스트
   ========================================================= */
const ENGINE = (() => {
  /* ① 확률표: 6/45 조합론 */
  const C45_6 = 8145060;
  const COUNT = {1:1, 2:6, 3:228, 4:11115, 5:182780};
  const P = {}; for (const k in COUNT) P[k] = COUNT[k] / C45_6;
  const P_ANY = 194130 / C45_6;                                  // 무엇이든 당첨 ≈ 2.38%
  const pAnyN = n => 1 - Math.pow(1 - P_ANY, n);
  const EXPECT_MATCH = 36 / 45;                                  // 세트당 기대 일치 0.8개
  const MATCH_SD = Math.sqrt(6 * (6/45) * (39/45) * (39/44));    // ≈ 0.784

  /* ② 진정 난수 결합 생성기: SHA-256 씨앗 xoshiro128** ⊕ crypto.getRandomValues */
  class Rng {
    constructor(seed32) {
      const v = new DataView(seed32.buffer, seed32.byteOffset, 32);
      this.s = [v.getUint32(0), v.getUint32(4), v.getUint32(8), v.getUint32(12)];
      if (this.s.every(x => x === 0)) this.s[0] = 1;
      this.buf = new Uint32Array(256); this.i = 256;
    }
    xo() {
      const s = this.s, m = Math.imul(s[1], 5), r = Math.imul((m << 7) | (m >>> 25), 9) >>> 0, t = s[1] << 9;
      s[2] ^= s[0]; s[3] ^= s[1]; s[1] ^= s[2]; s[0] ^= s[3]; s[2] ^= t; s[3] = (s[3] << 11) | (s[3] >>> 21);
      return r;
    }
    u32() { if (this.i >= 256) { crypto.getRandomValues(this.buf); this.i = 0; } return (this.xo() ^ this.buf[this.i++]) >>> 0; }
    float() { return this.u32() / 4294967296; }
    int(n) { const lim = Math.floor(0x100000000 / n) * n; let x; do { x = this.u32(); } while (x >= lim); return x % n; }
    combo() {
      const a = Array.from({length:45}, (_, i) => i + 1);
      for (let i = 0; i < 6; i++) { const j = i + this.int(45 - i); [a[i], a[j]] = [a[j], a[i]]; }
      return a.slice(0, 6).sort((x, y) => x - y);
    }
    // 가중치 비례 비복원 추출 (w[1..45], 제외 집합)
    weighted(w, k, chosen = []) {
      const out = chosen.slice();
      while (out.length < k) {
        let tot = 0; for (let n = 1; n <= 45; n++) if (!out.includes(n)) tot += w[n];
        if (tot <= 0) break;                                   // 고를 수 있는 번호가 없으면 중단
        let r = this.float() * tot, pick = -1, lastPos = -1;
        for (let n = 1; n <= 45; n++) { if (out.includes(n) || w[n] <= 0) continue; lastPos = n; r -= w[n]; if (r <= 0) { pick = n; break; } }
        if (pick < 0) pick = lastPos;                          // 부동소수 오차 대비: 마지막 후보

        if (!out.includes(pick)) out.push(pick);
      }
      return out.sort((a, b) => a - b);
    }
  }
  const randomSeed = () => { const s = new Uint8Array(32); crypto.getRandomValues(s); return s; };

  /* 데이터 압축: 번호 1~45를 문자 하나로 (6글자 = 1회차) */
  const ALPHA = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrs';
  const decode = str => { const o = []; for (let i = 0; i + 6 <= str.length; i += 6) o.push(Array.from(str.slice(i, i + 6), c => ALPHA.indexOf(c) + 1).sort((a, b) => a - b)); return o; };
  const encode = H => H.map(d => d.map(n => ALPHA[n - 1]).join('')).join('');

  /* ③ 데이터 분석: 번호별 5종 통계 + 궁합수 + 전이 행렬
     각 통계를 '순위'로 0~1 정규화한 뒤 평균 → 패턴 점수 (단위가 다른 지표를 공정하게 합치기 위함) */
  function analyze(H, recentN = 50) {
    const N = H.length, freq = Array(46).fill(0), rec = Array(46).fill(0), last = Array(46).fill(-1), r5 = Array(46).fill(0);
    const pair = Array.from({length:46}, () => new Float64Array(46));
    const trans = Array.from({length:46}, () => new Float64Array(46));
    H.forEach((d, i) => {
      for (const x of d) { freq[x]++; last[x] = i; if (i >= N - recentN) rec[x]++; if (i >= N - 5) r5[x]++; }
      for (let a = 0; a < 6; a++) for (let b = a + 1; b < 6; b++) { pair[d[a]][d[b]]++; pair[d[b]][d[a]]++; }
      if (i > 0) for (const m of H[i - 1]) for (const n of d) trans[m][n]++;
    });
    const gap = Array(46).fill(0), mom = Array(46).fill(0), markov = Array(46).fill(0);
    const lastDraw = H[N - 1] || [];
    for (let n = 1; n <= 45; n++) {
      gap[n] = N - 1 - last[n];
      mom[n] = rec[n] / Math.min(recentN, N) - freq[n] / N;
      for (const m of lastDraw) markov[n] += freq[m] ? trans[m][n] / freq[m] : 0;
    }
    const rankNorm = arr => {                       // 동점은 평균 순위
      const idx = Array.from({length:45}, (_, i) => i + 1).sort((a, b) => arr[a] - arr[b]);
      const out = Array(46).fill(0); let i = 0;
      while (i < 45) { let j = i; while (j + 1 < 45 && arr[idx[j + 1]] === arr[idx[i]]) j++; for (let k = i; k <= j; k++) out[idx[k]] = ((i + j) / 2) / 44; i = j + 1; }
      return out;
    };
    const F = { freq: rankNorm(freq), recent: rankNorm(rec), gap: rankNorm(gap), mom: rankNorm(mom), markov: rankNorm(markov) };
    const pattern = Array(46).fill(0);
    for (let n = 1; n <= 45; n++) pattern[n] = (F.freq[n] + F.recent[n] + F.gap[n] + F.mom[n] + F.markov[n]) / 5;
    let pairTot = 0; for (let a = 1; a <= 45; a++) for (let b = a + 1; b <= 45; b++) pairTot += pair[a][b];
    const nums = Array.from({length:45}, (_, i) => i + 1);
    const hot = nums.slice().sort((a, b) => rec[b] - rec[a] || freq[b] - freq[a]).slice(0, 10);
    const cold = nums.slice().sort((a, b) => gap[b] - gap[a]).slice(0, 10);
    const topPairs = [];
    for (let a = 1; a <= 45; a++) for (let b = a + 1; b <= 45; b++) topPairs.push([a, b, pair[a][b]]);
    topPairs.sort((x, y) => y[2] - x[2]);
    return { N, freq, rec, gap, mom, markov, F, pattern, pair, pairAvg: pairTot / 990, hot, cold, r5, lastDraw, topPairs: topPairs.slice(0, 40) };
  }

  /* ④ 군중 선호(인기도) 모델 — 사람들이 많이 고르는 특징일수록 점수 ↑ */
  function crowdScore(n, lastDraw) {
    let s = 0;
    for (const x of n) {
      if (x <= 31) s += 0.10; if (x <= 12) s += 0.04;
      if (x === 7) s += 0.15; else if (x === 3) s += 0.06; else if (x === 17 || x === 27) s += 0.04;
    }
    let run = 1, maxRun = 1;
    for (let i = 1; i < 6; i++) { run = n[i] === n[i-1] + 1 ? run + 1 : 1; maxRun = Math.max(maxRun, run); }
    if (maxRun >= 3) s += 0.5 * (maxRun - 2);
    const d = n[1] - n[0]; if (n.every((x, i) => i === 0 || x - n[i-1] === d)) s += 2.5;
    const tail = {}; n.forEach(x => tail[x % 10] = (tail[x % 10] || 0) + 1);
    const mt = Math.max(...Object.values(tail)); if (mt >= 3) s += 0.35 * (mt - 2);
    const col = {}, row = {};
    n.forEach(x => { col[(x-1)%7] = (col[(x-1)%7]||0) + 1; row[Math.floor((x-1)/7)] = (row[Math.floor((x-1)/7)]||0) + 1; });
    const mc = Math.max(...Object.values(col)), mr = Math.max(...Object.values(row));
    if (mc >= 4) s += 0.5 * (mc - 3); if (mr >= 4) s += 0.5 * (mr - 3);
    if (lastDraw && lastDraw.length) s += 0.3 * n.filter(x => lastDraw.includes(x)).length;
    return s;
  }
  const LAMBDA_AVG = 10;                                   // 가정: 평균 조합의 1등 공동 당첨자 약 10명
  const share = l => l < 1e-9 ? 1 : (1 - Math.exp(-l)) / l;   // E[1/(1+K)], K~Poisson(λ)
  function buildBaseline(rng, lastDraw, N = 20000) {
    const sc = new Float64Array(N); let wsum = 0;
    for (let i = 0; i < N; i++) { sc[i] = crowdScore(rng.combo(), lastDraw); wsum += Math.exp(sc[i]); }
    const meanW = wsum / N; let shSum = 0;
    for (let i = 0; i < N; i++) shSum += share(LAMBDA_AVG * Math.exp(sc[i]) / meanW);
    return { sorted: Array.from(sc).sort((a, b) => a - b), meanW, avgShare: shSum / N, lastDraw };
  }
  function percentile(base, s) {
    let lo = 0, hi = base.sorted.length; while (lo < hi) { const m = (lo + hi) >> 1; base.sorted[m] < s ? lo = m + 1 : hi = m; }
    let eq = lo; while (eq < base.sorted.length && base.sorted[eq] === s) eq++;
    return (lo + (eq - lo) / 2) / base.sorted.length;
  }
  const payoutMult = (base, s) => share(LAMBDA_AVG * Math.exp(s) / base.meanW) / base.avgShare;

  /* ⑤ 균형 필터: 역대 당첨번호의 '흔한 모양' (방법론 1) */
  function balance(n, A) {
    const fails = [], sum = n.reduce((a, b) => a + b, 0);
    if (sum < 120 || sum > 180) fails.push('합계');
    const odd = n.filter(x => x % 2).length; if (odd < 2 || odd > 4) fails.push('홀짝');
    const hi = n.filter(x => x >= 23).length; if (hi < 2 || hi > 4) fails.push('고저');
    const diffs = new Set(); for (let a = 0; a < 6; a++) for (let b = a + 1; b < 6; b++) diffs.add(n[b] - n[a]);
    const ac = diffs.size - 5; if (ac < 7) fails.push('AC');
    let cons = 0; for (let i = 1; i < 6; i++) if (n[i] === n[i-1] + 1) cons++; if (cons > 1) fails.push('연번');
    const tail = {}; n.forEach(x => tail[x % 10] = (tail[x % 10] || 0) + 1); if (Math.max(...Object.values(tail)) > 2) fails.push('끝수');
    if (new Set(n.map(x => Math.min(4, Math.floor((x - 1) / 10)))).size < 3) fails.push('번호대');
    if (A && n.some(x => A.r5[x] >= 2)) fails.push('과열');          // 최근 5회 2번 이상 나온 번호 배제
    return { ok: !fails.length, fails, sum, odd, hi, ac };
  }
  // 조건을 만족할 때까지 다시 뽑기 (최대 tries번, 실패 시 가장 덜 어긋난 것)
  function retry(make, A, tries = 400) {
    let best = null, bestF = 99;
    for (let t = 0; t < tries; t++) { const c = make(); const b = balance(c, A); if (b.ok) return c; if (b.fails.length < bestF) { best = c; bestF = b.fails.length; } }
    return best;
  }
  const overlap = (a, b) => a.filter(x => b.includes(x)).length;
  const distinctPush = (out, c) => { if (!out.some(o => overlap(o, c) >= 3 || o.join() === c.join())) { out.push(c); return true; } return false; };
  const meanPattern = (c, A) => c.reduce((s, x) => s + A.pattern[x], 0) / 6;
  function synergy(c, A) {
    let s = 0; for (let a = 0; a < 6; a++) for (let b = a + 1; b < 6; b++) s += A.pair[c[a]][c[b]];
    return Math.min(1, (s / 15) / (A.pairAvg * 2));
  }

  /* ⑥ 렌즈 8종: 같은 질문("어떤 6개?")에 서로 다른 관점으로 답하는 생성기 */
  const LENS = {
    // 회피: 후보 중 인기 하위 3% 풀에서 무작위 (모두가 같은 '최적'에 몰리지 않게)
    avoid(rng, ctx, k) {
      const cand = [], N = ctx.candN || 30000;
      for (let i = 0; i < N; i++) { const c = rng.combo(); cand.push({ c, s: crowdScore(c, ctx.lastDraw) }); }
      cand.sort((a, b) => a.s - b.s);
      const pool = cand.slice(0, Math.max(50, Math.floor(N * 0.03))), out = [];
      for (let t = 0; out.length < k && t < 3000; t++) distinctPush(out, pool[rng.int(pool.length)].c);
      return out;
    },
    // 선호: 내가 고른 번호 중심 + 빈자리는 인기 낮은 번호로 채워 몫 보호
    fav(rng, ctx, k) {
      const f = (ctx.fav || []).slice().sort((a, b) => a - b), out = [];
      if (!f.length) return out;
      const only = Array(46).fill(0).map((v, i) => f.includes(i) ? 1 : 0);
      for (let t = 0; out.length < k && t < 300; t++) {
        let c = f.length > 6 ? rng.weighted(only, 6) : f.slice();
        if (c.length < 6) {                       // 빈자리: 후보 40개 중 인기 가장 낮은 채움
          let best = null, bs = 1e9;
          for (let j = 0; j < 40; j++) { const x = rng.weighted(Array(46).fill(1), 6, c); const sc = crowdScore(x, ctx.lastDraw); if (sc < bs) { bs = sc; best = x; } }
          c = best;
        }
        // 선호 번호는 겹치는 게 당연하므로 '완전히 같은 세트'만 막음
        if (!out.some(o => o.join() === c.join())) out.push(c);
      }
      return out;
    },
    // 패턴: 빈도·최근빈도·갭·모멘텀·마르코프 5종 앙상블 점수에 비례 추출 + 균형 필터
    pattern(rng, ctx, k) {
      const w = ctx.A.pattern.map(p => Math.exp(4 * p)), out = [];
      for (let t = 0; out.length < k && t < 50; t++) distinctPush(out, retry(() => rng.weighted(w, 6), ctx.A));
      return out;
    },
    // 균형: 합계·홀짝·고저·AC·연번·끝수·번호대·과열 8중 필터를 통과한 무작위
    balance(rng, ctx, k) {
      const out = [];
      for (let t = 0; out.length < k && t < 50; t++) distinctPush(out, retry(() => rng.combo(), ctx.A, 2000));
      return out;
    },
    // 핫·콜드: 최근 50회 뜨거운 번호 3 + 오래 쉰 번호 2 + 나머지 1 (평균 회귀 가정)
    hotcold(rng, ctx, k) {
      const { hot, cold } = ctx.A, out = [];
      const coldOnly = cold.filter(x => !hot.includes(x));
      const make = () => {
        const one = (arr, w = Array(46).fill(0)) => { arr.forEach(x => w[x] = 1); return w; };
        let c = rng.weighted(one(hot), 3);
        c = rng.weighted(one(coldOnly.length >= 2 ? coldOnly : cold), 5, c);
        return rng.weighted(Array(46).fill(1), 6, c);
      };
      for (let t = 0; out.length < k && t < 50; t++) distinctPush(out, retry(make, ctx.A));
      return out;
    },
    // 궁합수: 역대 동반 출현이 많은 쌍에서 출발해, 함께 자주 나온 번호를 이어 붙임
    pair(rng, ctx, k) {
      const A = ctx.A, out = [];
      const make = () => {
        const p = A.topPairs[rng.int(A.topPairs.length)], c = [p[0], p[1]];
        while (c.length < 6) {
          const sc = []; for (let n = 1; n <= 45; n++) if (!c.includes(n)) sc.push([n, c.reduce((s, x) => s + A.pair[n][x], 0)]);
          sc.sort((a, b) => b[1] - a[1]); c.push(sc[rng.int(5)][0]);
        }
        return c.sort((a, b) => a - b);
      };
      for (let t = 0; out.length < k && t < 80; t++) distinctPush(out, retry(make, ctx.A, 150));
      return out;
    },
    // 마르코프: 지난 회차 번호들 다음에 자주 나왔던 번호(전이 확률) 비례 추출
    markov(rng, ctx, k) {
      const w = ctx.A.F.markov.map(p => Math.exp(3.5 * p)), out = [];
      for (let t = 0; out.length < k && t < 50; t++) distinctPush(out, retry(() => rng.weighted(w, 6), ctx.A));
      return out;
    },
    // 종합: 위 기준을 모두 적합도로 묶은 유전 알고리즘
    ga(rng, ctx, k) { return geneticSearch(rng, ctx, k); },
    // 대조군: 완전 무작위 (백테스트 비교용)
    random(rng, ctx, k) { const out = []; while (out.length < k) distinctPush(out, rng.combo()); return out; }
  };

  /* ⑦ 유전 알고리즘(방법론 2·5): 적합도 = 패턴 35% + 궁합 20% + 비인기 30% + 균형 15%
     교차: 두 부모 번호의 합집합에서 6개 무작위 / 돌연변이: 한 개를 무작위 번호로 교체 / 엘리트 보존 */
  function fitness(c, ctx) {
    const pop = ctx.base ? 1 - percentile(ctx.base, crowdScore(c, ctx.lastDraw)) : 0.5;
    return 0.35 * meanPattern(c, ctx.A) + 0.20 * synergy(c, ctx.A) + 0.30 * pop + (balance(c, ctx.A).ok ? 0.15 : 0);
  }
  function geneticSearch(rng, ctx, k, P = ctx.gaP || 120, G = ctx.gaG || 35) {
    let pop = Array.from({length:P}, () => { const c = rng.combo(); return { c, f: fitness(c, ctx) }; });
    const hall = pop.slice();                 // 명예의 전당: 진화 전 과정의 모든 해
    const pick = () => { let b = pop[rng.int(P)]; for (let i = 0; i < 2; i++) { const x = pop[rng.int(P)]; if (x.f > b.f) b = x; } return b; };
    for (let g = 0; g < G; g++) {
      pop.sort((a, b) => b.f - a.f);
      const next = pop.slice(0, 8);
      while (next.length < P) {
        const u = [...new Set([...pick().c, ...pick().c])];
        let c = rng.weighted(Array(46).fill(0).map((v, i) => u.includes(i) ? 1 : 0), Math.min(6, u.length));
        if (c.length < 6) c = rng.weighted(Array(46).fill(1), 6, c);
        if (rng.float() < 0.35) { const i = rng.int(6); let n; do { n = 1 + rng.int(45); } while (c.includes(n)); c[i] = n; c.sort((a, b) => a - b); }
        const ind = { c, f: fitness(c, ctx) }; next.push(ind); hall.push(ind);
      }
      pop = next;
    }
    pop.sort((a, b) => b.f - a.f);
    // 같은 데이터면 누구나 같은 최적해에 수렴 → 공유 시 모두 같은 번호가 되는 문제
    // 그래서 상위권의 서로 다른 해 최대 30개를 모은 뒤, 그중에서 무작위로 k개를 고름
    hall.sort((a, b) => b.f - a.f);
    const seen = new Set(), elite = [];
    for (const x of hall) { const key = x.c.join(); if (seen.has(key)) continue; seen.add(key); if (distinctPush(elite, x.c) && elite.length >= 60) break; }
    const out = [];
    for (let t = 0; out.length < k && elite.length && t < 200; t++) distinctPush(out, elite.splice(rng.int(elite.length), 1)[0]);
    // 수렴해서 다양한 답이 부족하면: 상위 해를 돌연변이시켜 적합도 높은 이웃을 찾아 채움
    for (let t = 0; out.length < k && t < 2000; t++) {
      const c = pop[rng.int(10)].c.slice(); for (let m = 0; m < 3; m++) { const i = rng.int(6); let n; do { n = 1 + rng.int(45); } while (c.includes(n)); c[i] = n; }
      c.sort((a, b) => a - b); if (fitness(c, ctx) > pop[P - 1].f) distinctPush(out, c);
    }
    while (out.length < k) distinctPush(out, rng.combo());
    return out;
  }

  /* 세트 꾸미기: 모든 세트에 같은 잣대(패턴·균형·인기도·몫)를 붙여 비교 가능하게 */
  function decorate(nums, lens, ctx) {
    const s = crowdScore(nums, ctx.lastDraw);
    return { nums, lens, pct: percentile(ctx.base, s), mult: payoutMult(ctx.base, s),
      pat: ctx.A ? meanPattern(nums, ctx.A) : null, bal: balance(nums, ctx.A).fails };
  }
  function generateAll(rng, ctx, perLens, lensIds) {
    const out = [];
    for (const id of lensIds) for (const c of LENS[id](rng, ctx, perLens)) out.push(decorate(c, id, ctx));
    return out;
  }

  /* ⑧ walk-forward 백테스트: t회차를 '그 이전 데이터만'으로 생성해 실제 결과와 비교 (미래 정보 누설 없음) */
  function backtestStep(H, t, rng, base, lensIds, k) {
    const A = analyze(H.slice(0, t)), ctx = { A, base, lastDraw: A.lastDraw, candN: 3000, gaP: 70, gaG: 20 };
    const res = {};
    for (const id of lensIds) res[id] = LENS[id](rng, ctx, k).map(c => overlap(c, H[t]));
    return res;
  }

  /* 렌즈 리그 통계: 같은 회차 세트끼리는 상관되므로 '회차 평균'을 표본 단위로 사용
     z → 양측 p값 → Holm-Bonferroni 보정(렌즈를 여러 개 비교하면 우연히 1등이 나오는 착시 방지) */
  const normCdf = z => { const t = 1 / (1 + 0.2316419 * Math.abs(z)), d = 0.3989423 * Math.exp(-z * z / 2);
    const p = d * t * (0.3193815 + t * (-0.3565638 + t * (1.781478 + t * (-1.821256 + t * 1.330274)))); return z > 0 ? 1 - p : p; };
  function league(perRound) {          // perRound: { lens: [[회차별 일치 배열], ...] }
    const rows = [];
    for (const id in perRound) {
      const r = perRound[id].filter(a => a.length).map(a => a.reduce((x, y) => x + y, 0) / a.length);
      if (!r.length) continue;
      const n = r.length, mean = r.reduce((a, b) => a + b, 0) / n;
      const sd = n > 1 ? Math.sqrt(r.reduce((a, b) => a + (b - mean) ** 2, 0) / (n - 1)) : MATCH_SD;
      const z = (mean - EXPECT_MATCH) / (Math.max(sd, 1e-9) / Math.sqrt(n));
      rows.push({ id, n, sets: perRound[id].reduce((a, b) => a + b.length, 0), mean, z, p: 2 * (1 - normCdf(Math.abs(z))) });
    }
    const cmp = rows.filter(r => r.id !== 'random').sort((a, b) => a.p - b.p);
    cmp.forEach((r, i) => { r.holm = Math.min(1, r.p * (cmp.length - i)); if (i) r.holm = Math.max(r.holm, cmp[i - 1].holm); });
    return rows.sort((a, b) => b.mean - a.mean);
  }

  function rank(nums, win, bonus) {
    const m = overlap(nums, win);
    if (m === 6) return { m, r: 1 }; if (m === 5 && bonus && nums.includes(bonus)) return { m, r: 2 };
    if (m === 5) return { m, r: 3 }; if (m === 4) return { m, r: 4 }; if (m === 3) return { m, r: 5 };
    return { m, r: 0 };
  }
  const PRIZE = { 4: 50000, 5: 5000 };
  async function sha256(bytes) { return new Uint8Array(await crypto.subtle.digest('SHA-256', bytes)); }
  const hex = b => Array.from(b, x => x.toString(16).padStart(2, '0')).join('');

  return { C45_6, P, P_ANY, pAnyN, EXPECT_MATCH, MATCH_SD, Rng, randomSeed, decode, encode, analyze, crowdScore,
    buildBaseline, percentile, payoutMult, balance, LENS, geneticSearch, decorate, generateAll, backtestStep, league, rank, PRIZE, sha256, hex, overlap };
})();
if (typeof module !== 'undefined') module.exports = ENGINE;
