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
      this.excl = null;                          // 제외수 집합(Set). 지정되면 모든 추출에서 빠짐
    }
    allowed() { const a = []; for (let n = 1; n <= 45; n++) if (!this.excl || !this.excl.has(n)) a.push(n); return a; }
    num() { const a = this.allowed(); return a[this.int(a.length)]; }
    xo() {
      const s = this.s, m = Math.imul(s[1], 5), r = Math.imul((m << 7) | (m >>> 25), 9) >>> 0, t = s[1] << 9;
      s[2] ^= s[0]; s[3] ^= s[1]; s[1] ^= s[2]; s[0] ^= s[3]; s[2] ^= t; s[3] = (s[3] << 11) | (s[3] >>> 21);
      return r;
    }
    u32() { if (this.i >= 256) { crypto.getRandomValues(this.buf); this.i = 0; } return (this.xo() ^ this.buf[this.i++]) >>> 0; }
    float() { return this.u32() / 4294967296; }
    int(n) { const lim = Math.floor(0x100000000 / n) * n; let x; do { x = this.u32(); } while (x >= lim); return x % n; }
    combo() {
      const a = this.allowed(), L = a.length;
      for (let i = 0; i < 6; i++) { const j = i + this.int(L - i); [a[i], a[j]] = [a[j], a[i]]; }
      return a.slice(0, 6).sort((x, y) => x - y);
    }
    // 가중치 비례 비복원 추출 (w[1..45], 제외 집합)
    weighted(w, k, chosen = []) {
      const out = chosen.slice();
      while (out.length < k) {
        let tot = 0; for (let n = 1; n <= 45; n++) if (!out.includes(n) && !(this.excl && this.excl.has(n))) tot += w[n];
        if (tot <= 0) break;                                   // 고를 수 있는 번호가 없으면 중단
        let r = this.float() * tot, pick = -1, lastPos = -1;
        for (let n = 1; n <= 45; n++) { if (out.includes(n) || w[n] <= 0 || (this.excl && this.excl.has(n))) continue; lastPos = n; r -= w[n]; if (r <= 0) { pick = n; break; } }
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
    // Lift = P(a∧b) / (P(a)·P(b)) : 자주 나오는 번호끼리 우연히 자주 만나는 효과를 걷어낸 '진짜 궁합'
    // 표본이 적은 쌍의 과장을 막기 위해 평균 동반 횟수만큼 가상 표본을 더해 수축(shrinkage)
    const lift = Array.from({length:46}, () => new Float64Array(46));
    const pAvg = pairTot / 990;
    for (let a = 1; a <= 45; a++) for (let b = 1; b <= 45; b++) if (a !== b) {
      const expd = freq[a] * freq[b] / Math.max(1, N);          // 독립 가정 기대 동반 수
      lift[a][b] = (pair[a][b] + pAvg) / (expd + pAvg);
    }
    const nums = Array.from({length:45}, (_, i) => i + 1);
    const hot = nums.slice().sort((a, b) => rec[b] - rec[a] || freq[b] - freq[a]).slice(0, 10);
    const cold = nums.slice().sort((a, b) => gap[b] - gap[a]).slice(0, 10);
    const topPairs = [];
    for (let a = 1; a <= 45; a++) for (let b = a + 1; b <= 45; b++) topPairs.push([a, b, pair[a][b], lift[a][b]]);
    topPairs.sort((x, y) => y[3] - x[3]);
    return { N, freq, rec, gap, mom, markov, F, pattern, pair, lift, pairAvg: pairTot / 990, hot, cold, r5, lastDraw, topPairs: topPairs.slice(0, 40) };
  }

  /* ④ 군중 선호(인기도) 모델
     LOTTO LAB Phase 3에서 실제 1등 당첨자 수로 추정한 quasi-Poisson 계수(표준편차당 효과)를 사용
       합계 +1SD → 당첨자 -4.9% · 같은 줄 최대 +1SD → -7.4% · 같은 끝수 최대 +1SD → +5.9% · 직전 회차 겹침 +1SD → -1.4%
     여기에, 표본이 드물어 회귀로는 잡히지 않는 '대중 패턴'(등차수열, 4연속 이상, 행운수 7 등)을 가산
     점수 s는 log(상대 인기도): s가 클수록 같은 조합을 산 사람이 많다고 추정 */
  const Z = { sum: [138.07, 29.95], row: [2.203, 0.554], tail: [1.882, 0.542], prev: [0.799, 0.784] };
  function crowdScore(n, lastDraw) {
    const sum = n.reduce((a, b) => a + b, 0), row = {}, tail = {};
    n.forEach(x => { row[Math.floor((x-1)/7)] = (row[Math.floor((x-1)/7)]||0) + 1; tail[x % 10] = (tail[x % 10]||0) + 1; });
    const rmax = Math.max(...Object.values(row)), tmax = Math.max(...Object.values(tail));
    const prev = lastDraw && lastDraw.length ? n.filter(x => lastDraw.includes(x)).length : Z.prev[0];
    const z = (v, k) => (v - Z[k][0]) / Z[k][1];
    let s = Math.log(1 - 0.049) * z(sum, 'sum') + Math.log(1 - 0.074) * z(rmax, 'row') + Math.log(1 + 0.059) * z(tmax, 'tail') + Math.log(1 - 0.014) * z(prev, 'prev');
    // 하드 패턴(대중이 '그림'이나 '규칙'으로 고르는 조합)
    let run = 1, maxRun = 1;
    for (let i = 1; i < 6; i++) { run = n[i] === n[i-1] + 1 ? run + 1 : 1; maxRun = Math.max(maxRun, run); }
    if (maxRun >= 4) s += 0.8 * (maxRun - 3);
    const d = n[1] - n[0]; if (n.every((x, i) => i === 0 || x - n[i-1] === d)) s += 2.0;
    if (n.every(x => x % 5 === 0) || n.every(x => x % 7 === 0)) s += 1.2;
    if (n.includes(7)) s += 0.05;
    return s;
  }
  const LAMBDA_AVG = 11;                                   // 실제 회차당 평균 1등 약 12명 → 내가 당첨일 때 다른 공동 당첨자 약 11명
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
    if (A && n.some(x => A.r5[x] >= 2)) fails.push('과열');
    // 정보 엔트로피: 번호 사이 간격 5개의 섀넌 엔트로피. 간격이 반복되면(규칙적 패턴) 낮아짐 → 지나치게 단순한 조합 탈락
    const gaps = {}; for (let i = 1; i < 6; i++) { const g = n[i] - n[i-1]; gaps[g] = (gaps[g] || 0) + 1; }
    let ent = 0; for (const g in gaps) { const p = gaps[g] / 5; ent -= p * Math.log2(p); }
    if (ent < 1.5) fails.push('엔트로피');          // 최근 5회 2번 이상 나온 번호 배제
    return { ok: !fails.length, fails, sum, odd, hi, ac, ent };
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
      for (let t = 0; out.length < k && t < 300; t++) distinctPush(out, retry(() => rng.weighted(w, 6), ctx.A));
      return out;
    },
    // 균형: 합계·홀짝·고저·AC·연번·끝수·번호대·과열 8중 필터를 통과한 무작위
    balance(rng, ctx, k) {
      const out = [];
      for (let t = 0; out.length < k && t < 300; t++) distinctPush(out, retry(() => rng.combo(), ctx.A, 2000));
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
      for (let t = 0; out.length < k && t < 300; t++) distinctPush(out, retry(make, ctx.A));
      return out;
    },
    // 궁합수: Lift(진짜 궁합)가 높은 쌍에서 출발해, 궁합 합이 큰 번호를 이어 붙임 (네트워크 확장)
    pair(rng, ctx, k) {
      const A = ctx.A, out = [];
      const make = () => {
        const okPairs = A.topPairs.filter(q => !(rng.excl && (rng.excl.has(q[0]) || rng.excl.has(q[1]))));
        const p = okPairs[rng.int(okPairs.length)], c = [p[0], p[1]];
        while (c.length < 6) {
          const sc = []; for (let n = 1; n <= 45; n++) if (!c.includes(n) && !(rng.excl && rng.excl.has(n))) sc.push([n, c.reduce((s, x) => s + A.lift[n][x], 0)]);
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
      for (let t = 0; out.length < k && t < 300; t++) distinctPush(out, retry(() => rng.weighted(w, 6), ctx.A));
      return out;
    },
    // 머신러닝: 로지스틱 회귀가 번호별 '다음 회차 출현 확률'을 추정 → 확률 순위에 비례 추출
    ml(rng, ctx, k) {
      if (!ctx.ml) ctx.ml = mlTrain(ctx.H, ctx.H.length);
      const p = mlPredict(ctx.ml, ctx.H, ctx.H.length), w = rankWeights(p, 4), out = [];
      for (let t = 0; out.length < k && t < 300; t++) distinctPush(out, retry(() => rng.weighted(w, 6), ctx.A));
      return out;
    },
    // 개미 군집(ACO): 45개 번호 그래프에서 개미들이 페로몬(궁합)과 휴리스틱(패턴)을 따라 6개 경로를 만들고,
    // 좋은 경로(적합도↑)에 페로몬을 더 남기며 반복 → 군집 지능이 찾은 조합
    aco(rng, ctx, k) { return antColony(rng, ctx, k); },
    // 종합: 위 기준을 모두 적합도로 묶은 유전 알고리즘
    ga(rng, ctx, k) { return geneticSearch(rng, ctx, k); },
    // 물리 추첨기: 45개 공을 원형 드럼에 넣고 중력·바닥 공기 분사·충돌을 시뮬레이션해 위쪽 배출구로 나온 공 6개
    physics(rng, ctx, k) { const out = []; for (let t = 0; out.length < k && t < 30; t++) distinctPush(out, drumSim(rng)); return out; },
    // 우주 난수: 공개 난수 비콘(drand) + 실시간 지진 데이터 + 손끝 씨앗을 SHA-256으로 섞은 씨앗으로 추출
    cosmic(rng, ctx, k) {
      const r2 = ctx.cosmicSeed ? new Rng(ctx.cosmicSeed) : rng, out = []; r2.excl = rng.excl;
      while (out.length < k) distinctPush(out, r2.combo());
      return out;
    },
    // 이월·이웃: 지난 회차 번호 1개(이월수) + 그 ±1 이웃수 2~3개 + 나머지 (국내 전통 패턴 기법)
    carry(rng, ctx, k) {
      const last = ctx.A.lastDraw, out = [];
      const nb = [...new Set(last.flatMap(x => [x - 1, x + 1]))].filter(x => x >= 1 && x <= 45 && !last.includes(x));
      const one = arr => { const w = Array(46).fill(0); arr.forEach(x => w[x] = 1); return w; };
      const make = () => { let c = rng.weighted(one(last), 1); c = rng.weighted(one(nb), 3 + (rng.float() < 0.5 ? 1 : 0), c); return rng.weighted(Array(46).fill(1), 6, c); };
      for (let t = 0; out.length < k && t < 300; t++) distinctPush(out, retry(make, ctx.A));
      return out;
    },
    // 행운의 단어: 꿈·기념일·소원 같은 단어 + 손끝 씨앗을 SHA-256으로 섞은 씨앗 (같은 단어라도 사람마다 다른 번호)
    word(rng, ctx, k) {
      if (!ctx.wordSeed) return [];
      const r2 = new Rng(ctx.wordSeed); r2.excl = rng.excl; const out = [];
      for (let t = 0; out.length < k && t < 300; t++) distinctPush(out, r2.combo());
      return out;
    },
    // 휠링(축소 조합): 선호 번호 v개(7~12) 중 t개가 당첨번호에 들어가면, 적어도 한 장은 그 t개를 모두 포함하도록 보장하는 최소 조합
    wheel(rng, ctx) { const f = (ctx.fav || []).filter(x => !(rng.excl && rng.excl.has(x))); return f.length >= 7 ? buildWheel(rng, f, ctx.wheelT || 3).tickets : []; },
    // 대조군: 완전 무작위 (백테스트 비교용)
    random(rng, ctx, k) { const out = []; while (out.length < k) distinctPush(out, rng.combo()); return out; }
  };

  const rankWeights = (p, beta) => {
    const idx = Array.from({length:45}, (_, i) => i + 1).sort((a, b) => p[a] - p[b]), w = Array(46).fill(0);
    idx.forEach((n, i) => w[n] = Math.exp(beta * i / 44)); return w;
  };

  /* ML: 번호별 피처 6종을 회차 순서대로 '누적 계산'(미래 정보 없음)
     [전체 출현율, 최근 50회 출현율, 최근 10회 출현율, log(1+미출현 간격), 직전 회차 출현 여부, 마르코프 전이 점수] */
  function mlFeatures(H, tFrom, tTo, onRow) {
    const freq = Array(46).fill(0), last = Array(46).fill(-1);
    const trans = Array.from({length:46}, () => new Float64Array(46));
    const f = new Float64Array(6);
    for (let t = 0; t < tTo; t++) {
      if (t >= tFrom && t > 0) {
        const prev = H[t - 1], w50 = Math.min(50, t), w10 = Math.min(10, t);
        const c50 = Array(46).fill(0), c10 = Array(46).fill(0);
        for (let j = t - w50; j < t; j++) for (const x of H[j]) { c50[x]++; if (j >= t - w10) c10[x]++; }
        for (let n = 1; n <= 45; n++) {
          let mk = 0; for (const m of prev) mk += freq[m] ? trans[m][n] / freq[m] : 0;
          f[0] = freq[n] / t; f[1] = c50[n] / w50; f[2] = c10[n] / w10; f[3] = Math.log1p(last[n] < 0 ? t : t - 1 - last[n]);
          f[4] = prev.includes(n) ? 1 : 0; f[5] = mk;
          onRow(t, n, f, H[t] ? (H[t].includes(n) ? 1 : 0) : null);
        }
      }
      if (t < H.length) { for (const x of H[t]) { freq[x]++; last[x] = t; } if (t > 0) for (const m of H[t - 1]) for (const x of H[t]) trans[m][x]++; }
    }
  }
  // 로지스틱 회귀: 최근 400회차(최대 18,000 샘플)로 표준화 → 경사하강 + L2 규제
  function mlTrain(H, upto) {
    const from = Math.max(60, upto - 400), X = [], y = [];
    mlFeatures(H, from, upto, (t, n, f, lab) => { X.push(Array.from(f)); y.push(lab); });
    const d = 6, mu = Array(d).fill(0), sd = Array(d).fill(0);
    X.forEach(r => r.forEach((v, j) => mu[j] += v / X.length));
    X.forEach(r => r.forEach((v, j) => sd[j] += (v - mu[j]) ** 2 / X.length));
    for (let j = 0; j < d; j++) sd[j] = Math.sqrt(sd[j]) || 1;
    const Xs = X.map(r => r.map((v, j) => (v - mu[j]) / sd[j]));
    let w = Array(d).fill(0), b = Math.log(6 / 39);
    for (let it = 0; it < 150; it++) {
      const g = Array(d).fill(0); let gb = 0;
      for (let i = 0; i < Xs.length; i++) {
        let z = b; for (let j = 0; j < d; j++) z += w[j] * Xs[i][j];
        const e = 1 / (1 + Math.exp(-z)) - y[i]; gb += e; for (let j = 0; j < d; j++) g[j] += e * Xs[i][j];
      }
      for (let j = 0; j < d; j++) w[j] -= 0.5 * (g[j] / Xs.length + 0.01 * w[j]);
      b -= 0.5 * gb / Xs.length;
    }
    return { w, b, mu, sd, n: Xs.length };
  }
  function mlPredict(m, H, t) {
    const p = Array(46).fill(0);
    mlFeatures(H, t, t + 1, (tt, n, f) => { let z = m.b; for (let j = 0; j < 6; j++) z += m.w[j] * (f[j] - m.mu[j]) / m.sd[j]; p[n] = 1 / (1 + Math.exp(-z)); });
    return p;
  }

  /* 개미 군집 최적화(ACO) */
  function antColony(rng, ctx, k, ants = 24, iters = 25) {
    const A = ctx.A, tau = Array.from({length:46}, (_, a) => Float64Array.from({length:46}, (_, b) => a && b && a !== b ? A.lift[a][b] : 0));
    const eta = Array(46).fill(0).map((v, n) => n ? Math.exp(2 * A.pattern[n]) : 0);
    const hall = [];
    for (let it = 0; it < iters; it++) {
      const sols = [];
      for (let a = 0; a < ants; a++) {
        const c = rng.weighted(eta, 1);
        while (c.length < 6) {
          const w = Array(46).fill(0);
          for (let n = 1; n <= 45; n++) if (!c.includes(n)) { let t = 0; for (const x of c) t += tau[x][n]; w[n] = Math.pow(t / c.length, 2) * eta[n]; }
          c.push(rng.weighted(w, 1)[0]);
        }
        c.sort((x, y) => x - y); const ind = { c, f: fitness(c, ctx) }; sols.push(ind); hall.push(ind);
      }
      for (let a = 1; a <= 45; a++) for (let b = 1; b <= 45; b++) tau[a][b] *= 0.9;          // 증발
      sols.sort((x, y) => y.f - x.f);
      for (const s of sols.slice(0, 5)) for (const x of s.c) for (const y of s.c) if (x !== y) tau[x][y] += s.f;   // 상위 개미가 페로몬 남김
    }
    hall.sort((x, y) => y.f - x.f);
    const seen = new Set(), elite = [];
    for (const x of hall) { const key = x.c.join(); if (seen.has(key)) continue; seen.add(key); if (distinctPush(elite, x.c) && elite.length >= 60) break; }
    const out = []; while (out.length < k && elite.length) distinctPush(out, elite.splice(rng.int(elite.length), 1)[0]);
    while (out.length < k) distinctPush(out, rng.combo());
    return out;
  }

  /* 물리 추첨기 시뮬레이션: 원형 드럼(반지름 1) 속 공 45개, 중력 + 바닥 공기 분사(무작위 세기) + 공끼리 탄성 충돌
     워밍업 뒤 일정 간격마다 배출구(맨 위)에 가장 가까운 공을 한 개씩 꺼냄. 초기 조건 미세 차이가 결과를 완전히 바꾸는 카오스계 */
  function drumSim(rng) {
    const R = 1, r = 0.075, balls = [];
    for (const num of rng.allowed()) { let x, y; do { x = (rng.float() * 2 - 1) * 0.85; y = -rng.float() * 0.85; } while (x * x + y * y > 0.72); balls.push({ n: num, x, y, vx: 0, vy: 0 }); }
    const out = [], dt = 0.012;
    for (let step = 0; out.length < 6 && step < 4000; step++) {
      for (const b of balls) {
        b.vy -= 9.8 * dt * 0.3;                                                        // 중력
        if (b.y < -0.55) { b.vy += (2.5 + rng.float() * 3) * dt * 4; b.vx += (rng.float() - 0.5) * dt * 6; }   // 바닥 공기 분사
        b.x += b.vx * dt; b.y += b.vy * dt;
        const d = Math.hypot(b.x, b.y);
        if (d > R - r) { const nx = b.x / d, ny = b.y / d, vn = b.vx * nx + b.vy * ny; if (vn > 0) { b.vx -= 1.9 * vn * nx; b.vy -= 1.9 * vn * ny; } b.x = nx * (R - r); b.y = ny * (R - r); }
      }
      for (let i = 0; i < balls.length; i++) for (let j = i + 1; j < balls.length; j++) {     // 탄성 충돌
        const a = balls[i], c = balls[j], dx = c.x - a.x, dy = c.y - a.y, dd = Math.hypot(dx, dy);
        if (dd > 0 && dd < 2 * r) {
          const nx = dx / dd, ny = dy / dd, rel = (c.vx - a.vx) * nx + (c.vy - a.vy) * ny, ov = (2 * r - dd) / 2;
          a.x -= nx * ov; a.y -= ny * ov; c.x += nx * ov; c.y += ny * ov;
          if (rel < 0) { a.vx += rel * nx; a.vy += rel * ny; c.vx -= rel * nx; c.vy -= rel * ny; }
        }
      }
      if (step > 300 && step % 80 === 0) {                                               // 배출구: 맨 위(0, 1)에 가장 가까운 공
        let bi = 0, bd = 9; balls.forEach((b, i) => { const dd = Math.hypot(b.x, b.y - 1); if (dd < bd) { bd = dd; bi = i; } });
        out.push(balls.splice(bi, 1)[0].n);
      }
    }
    return out.sort((a, b) => a - b);
  }

  /* 휠링: 커버링 설계를 탐욕법으로 구성
     t-부분집합(예: 10개 중 3개씩 120가지)을 모두 '덮을' 때까지, 아직 덮지 못한 t-부분집합을 가장 많이 덮는 6개 조합을 하나씩 추가 */
  const kSubsets = (arr, k) => { const out = []; const rec = (st, cur) => { if (cur.length === k) { out.push(cur.slice()); return; } for (let i = st; i < arr.length; i++) { cur.push(arr[i]); rec(i + 1, cur); cur.pop(); } }; rec(0, []); return out; };
  function buildWheel(rng, pool, t) {
    const p = pool.slice(); for (let i = p.length - 1; i > 0; i--) { const j = rng.int(i + 1); [p[i], p[j]] = [p[j], p[i]]; }   // 사람마다 다른 휠
    const uncovered = new Set(kSubsets(p, t).map(x => x.sort((a, b) => a - b).join(',')));
    const cands = kSubsets(p, 6).map(c => c.sort((a, b) => a - b)), coverMap = cands.map(c => kSubsets(c, t).map(x => x.join(',')));
    const tickets = [];
    while (uncovered.size && tickets.length < 60) {
      let bi = 0, bc = -1;
      coverMap.forEach((keys, i) => { let cnt = 0; for (const key of keys) if (uncovered.has(key)) cnt++; if (cnt > bc) { bc = cnt; bi = i; } });
      tickets.push(cands[bi]); coverMap[bi].forEach(key => uncovered.delete(key));
    }
    return { tickets, t, v: p.length, complete: uncovered.size === 0 };
  }

  /* 커버리지: 무작위 추첨을 n번 가상으로 돌려, 세트 묶음 중 '하나라도 5등 이상'이 나오는 비율을 추정 (몬테카를로)
     같은 장수라도 세트끼리 번호가 덜 겹치면 이 확률이 조금 올라감. 기대 당첨금은 장수가 같으면 동일 */
  function simDraws(n = 20000) { const r = new Rng(randomSeed()), d = []; for (let i = 0; i < n; i++) d.push(r.combo()); return d; }
  function hitMatrix(sets, draws) { return sets.map(c => Uint8Array.from(draws, d => overlap(c, d) >= 3 ? 1 : 0)); }
  function anyHitRate(M, idx) { const n = M[0] ? M[0].length : 0; let h = 0; for (let j = 0; j < n; j++) if (idx.some(i => M[i][j])) h++; return n ? h / n : 0; }
  function optimizeCoverage(M, K) {        // 탐욕법: 매번 '추가로 덮는 추첨'이 가장 많은 세트를 고름
    const n = M[0].length, hit = new Uint8Array(n), chosen = [];
    while (chosen.length < Math.min(K, M.length)) {
      let bi = -1, bg = -1;
      M.forEach((row, i) => { if (chosen.includes(i)) return; let g = 0; for (let j = 0; j < n; j++) if (row[j] && !hit[j]) g++; if (g > bg) { bg = g; bi = i; } });
      chosen.push(bi); for (let j = 0; j < n; j++) if (M[bi][j]) hit[j] = 1;
    }
    return chosen;
  }

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
        if (rng.float() < 0.35) { const i = rng.int(6); let n; do { n = rng.num(); } while (c.includes(n)); c[i] = n; c.sort((a, b) => a - b); }
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
      const c = pop[rng.int(10)].c.slice(); for (let m = 0; m < 3; m++) { const i = rng.int(6); let n; do { n = rng.num(); } while (c.includes(n)); c[i] = n; }
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
  function backtestStep(H, t, rng, base, lensIds, k, cache = {}) {
    const Ht = H.slice(0, t), A = analyze(Ht);
    // ML은 백테스트 시작 시점까지의 데이터로 한 번만 학습(이후 회차 정보 누설 없음)
    if (lensIds.includes('ml') && !cache.ml) cache.ml = mlTrain(H, t);
    const ctx = { A, H: Ht, base, lastDraw: A.lastDraw, candN: 3000, gaP: 70, gaG: 20, ml: cache.ml };
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
    buildBaseline, percentile, payoutMult, balance, LENS, mlTrain, mlPredict, drumSim, buildWheel, kSubsets, simDraws, hitMatrix, anyHitRate, optimizeCoverage, geneticSearch, decorate, generateAll, backtestStep, league, rank, PRIZE, sha256, hex, overlap };
})();
if (typeof module !== 'undefined') module.exports = ENGINE;
