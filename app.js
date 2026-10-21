// ==========================================================
// 空間偏好 AR：視野版（手機網頁）
//
// 後鏡頭拍到的真實空間 → 套用遊戲裡的視野規則：
//   中央區清晰；中央區邊緣是逐級縮小、機率遞減的清晰方塊；
//   外圍全黑，只留下白色小圓點（依邊緣與亮度）與空心方框標記。
// 手機的方向感測器決定視線；走路步伐（加速度計）或「按住前進」決定位置。
// 依你的移動習慣，在眼前生成白色線條構成的虛擬建築（單位：公尺）。
//
// v2 新增：
//   空間偵測（角點特徵、垂直線、地板測距、近似語義分割）→ 世界模型（地板、牆、柱、轉角）
//   虛擬建築附著於世界模型長出來（不再隨機落地）
//   右上角：陀螺儀 + 羅盤方位
//   隨機移動時觸發 AR 懸疑場景
// ==========================================================
(() => {
'use strict';

const DEG = Math.PI / 180;
const $ = (id) => document.getElementById(id);
const clamp01 = (v) => (v < 0 ? 0 : v > 1 ? 1 : v);
const lerp = (a, b, t) => a + (b - a) * t;
const rand = (a, b) => a + Math.random() * (b - a);

// ---------- 畫布 ----------
const cv = $('view');
const ctx = cv.getContext('2d');
const scene = document.createElement('canvas'); // 鏡頭影像 + 虛擬建築
const sctx = scene.getContext('2d');
const sm = document.createElement('canvas'); // 低解析度副本，供分析用
const smctx = sm.getContext('2d', { willReadFrequently: true });
const video = $('cam');

let W = 0, H = 0, DPR = 1, U = 1;
const SAMPLE = 5;
let AW = 0, AH = 0;
let gray = new Float32Array(1);
let edgeMag = new Float32Array(1);
let bandEdge = [0], BAND_TOTAL = 1;

// ---------- 設定 ----------
const S = {
  sizeMul: 1, // 中央區大小倍率
  fovLong: 65, // 相機長邊視角（度）
  stepLen: 0.7, // 一步的長度（公尺）
  dotThreshold: 14,
  dotDensity: 4,
  dotMin: 0.7,
  dotMax: 1.6,
  dotFalloff: 320,
  markerCount: 18,
  bandCell: [25, 12.5, 6.25],
  bandWidth: [50, 37.5, 25],
  bandPow: 1.4,
  limitOn: true,
  showHud: true,
  showDet: false, // 偵測層（語義色塊、特徵點、垂直線、距離、Canny 邊緣、物體框）：後台運作，預設不顯示；網址加 ?debug=1 可打開
  cannyOn: true, // 用 Canny 細邊緣取代 Sobel 閾值（垂直線、轉角、外圍點雲、標記物挑位）
  showCanny: false, // 疊圖顯示 Canny 邊緣（需 showDet）
  people: true, // 人物偵測：拿手機的人＝連機玩家＝敵人
  freeGen: false, // 自由生成（不依附偵測結果；僅供桌機測試）
};
// 遊戲裡的中央區（左右各 50°、上 50°、下 58°）在 1000×675 畫面上的比例
const CEN_X = 0.2064; // 半寬 / 畫面寬
const CEN_UP = 0.3058; // 上緣到中心 / 畫面高
const CEN_DOWN = 0.4107; // 下緣到中心 / 畫面高

function loadSettings() {
  try {
    const raw = localStorage.getItem('arVision.v2');
    if (raw) Object.assign(S, JSON.parse(raw));
  } catch (e) { /* 沒有儲存空間也沒關係 */ }
}
function saveSettings() {
  try { localStorage.setItem('arVision.v2', JSON.stringify({ sizeMul: S.sizeMul, fovLong: S.fovLong, stepLen: S.stepLen, dotThreshold: S.dotThreshold, showHud: S.showHud, cannyOn: S.cannyOn, people: S.people })); } catch (e) { /* ignore */ }
}

// ==========================================================
// 狀態
// ==========================================================
let running = false;
let C = { l: 0, r: 0, t: 0, b: 0 };
const EYE = 1.5; // 眼睛離地（公尺）
const pos = { x: 0, z: 0 };
let pending = 0; // 還沒走完的距離（公尺）
let moveSpeed = 0; // 實際移動速度（公尺/秒）
let steps = 0;
let holdWalk = false;
let lastT = 0;
let detTick = 0;
let timeSinceStart = 0;

// 視線基底（遊戲座標：x 右、y 上、z 朝後；起始朝 -z）
let B = { sr: [1, 0, 0], su: [0, 1, 0], F: [0, 0, -1] };
let FPX = 600; // 焦距（像素）
let hasSensor = false;
let sensor = { a: 0, b: 90, g: 0, seen: false };
let h0 = null; // 校準時的羅盤方位（弧度）
let yawM = 0, pitchM = 0; // 沒有感測器時用拖曳轉動
let headX = 0, headZ = -1; // 水平朝向（單位向量）
let prevYaw = 0;

// ==========================================================
// 尺寸
// ==========================================================
function resize() {
  DPR = Math.min(window.devicePixelRatio || 1, 2);
  W = Math.max(200, window.innerWidth);
  H = Math.max(200, window.innerHeight);
  for (const c of [cv, scene]) {
    c.width = Math.round(W * DPR);
    c.height = Math.round(H * DPR);
  }
  cv.style.width = W + 'px';
  cv.style.height = H + 'px';
  AW = Math.ceil(W / SAMPLE);
  AH = Math.ceil(H / SAMPLE);
  sm.width = AW;
  sm.height = AH;
  gray = new Float32Array(AW * AH);
  edgeMag = new Float32Array(AW * AH);
  U = Math.min(1.1, Math.max(0.55, Math.min(W, H) / 560));
  bandEdge = [0];
  for (let i = 0; i < S.bandWidth.length; i++) bandEdge.push(bandEdge[i] + S.bandWidth[i] * U);
  BAND_TOTAL = bandEdge[bandEdge.length - 1];
  C = centerRect();
  detectResize();
  SAFE_TOP = safeTop();
}
window.addEventListener('resize', resize);
window.addEventListener('orientationchange', () => setTimeout(resize, 200));

// ==========================================================
// 感測器
// ==========================================================
function screenAngle() {
  let a = 0;
  if (screen.orientation && typeof screen.orientation.angle === 'number') a = screen.orientation.angle;
  else if (typeof window.orientation === 'number') a = window.orientation;
  return ((a % 360) + 360) % 360;
}

function e2g(v) {
  // 地球座標（東、北、上）→ 遊戲座標，起始朝向（h0）對應遊戲的 -z
  const h = Math.atan2(v[0], v[1]);
  const th = h - h0;
  const rho = Math.hypot(v[0], v[1]);
  return [rho * Math.sin(th), v[2], -rho * Math.cos(th)];
}

function sensorBasis() {
  const x = sensor.b * DEG, y = sensor.g * DEG, z = sensor.a * DEG;
  const cX = Math.cos(x), cY = Math.cos(y), cZ = Math.cos(z);
  const sX = Math.sin(x), sY = Math.sin(y), sZ = Math.sin(z);
  const m11 = cZ * cY - sZ * sX * sY, m12 = -cX * sZ, m13 = cY * sZ * sX + cZ * sY;
  const m21 = cY * sZ + cZ * sX * sY, m22 = cZ * cX, m23 = sZ * sY - cZ * cY * sX;
  const m31 = -cX * sY, m32 = sX, m33 = cX * cY;
  const Re = [m11, m21, m31]; // 螢幕右（直立持機）
  const Ue = [m12, m22, m32]; // 螢幕上
  const Fe = [-m13, -m23, -m33]; // 後鏡頭朝向
  if (h0 === null) {
    const hf = Math.hypot(Fe[0], Fe[1]) > 0.3 ? Fe : Ue;
    h0 = Math.atan2(hf[0], hf[1]);
  }
  let r = e2g(Re), u = e2g(Ue);
  const f = e2g(Fe);
  // 螢幕旋轉（橫放）修正
  const ang = screenAngle();
  let sr = r, su = u;
  if (ang === 90) { sr = u.map((q) => -q); su = r; }
  else if (ang === 180) { sr = r.map((q) => -q); su = u.map((q) => -q); }
  else if (ang === 270) { sr = u; su = r.map((q) => -q); }
  return { sr, su, F: f, up: u };
}

function manualBasis() {
  const cy = Math.cos(yawM), sy = Math.sin(yawM), cp = Math.cos(pitchM), sp = Math.sin(pitchM);
  return {
    sr: [cy, 0, sy],
    su: [-sy * sp, cp, cy * sp],
    F: [sy * cp, sp, -cy * cp],
    up: [-sy * sp, cp, cy * sp],
  };
}

function updateCamera() {
  const nb = hasSensor && sensor.seen ? sensorBasis() : manualBasis();
  B = nb;
  // 水平朝向：看地面或天花板時改用手機「上緣」的方向
  let hx = nb.F[0], hz = nb.F[2];
  let hl = Math.hypot(hx, hz);
  if (hl < 0.35) {
    const s = nb.F[1] < 0 ? 1 : -1;
    hx = nb.up[0] * s;
    hz = nb.up[2] * s;
    hl = Math.hypot(hx, hz);
  }
  if (hl > 1e-4) {
    headX = hx / hl;
    headZ = hz / hl;
  }
}

function dot3(a, b) { return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]; }

// 世界點（相對於眼睛的向量）→ 相機座標
function toCam(vx, vy, vz) {
  const v = [vx, vy, vz];
  return [dot3(v, B.sr), dot3(v, B.su), dot3(v, B.F)];
}
function toScreen(c) {
  return [W / 2 + (FPX * c[0]) / c[2], H / 2 - (FPX * c[1]) / c[2]];
}

// ==========================================================
// 視野：中央區與動態縮放
// ==========================================================
const fov = { l: 1, r: 1, u: 1, d: 1, move: 0, prox: { l: 0, r: 0, f: 0 } };
const FOV_MIN = 0.3, MOVE_SHRINK = 0.3, SIDE_SHRINK = 0.6, FRONT_SHRINK = 0.35;
const COVER_RANGE = 3.0; // 公尺
const FOV_IN = 0.2, FOV_OUT = 0.06;

function centerRect() {
  const k = S.sizeMul;
  const kx = k * (W < H ? 1.3 : 1); // 直立時畫面較窄，水平方向多給一些
  return {
    l: Math.max(0, W / 2 - CEN_X * W * kx * fov.l),
    r: Math.min(W, W / 2 + CEN_X * W * kx * fov.r),
    t: Math.max(0, H / 2 - CEN_UP * H * k * fov.u),
    b: Math.min(H, H / 2 + CEN_DOWN * H * k * fov.d),
  };
}

function rectDist(x, y) {
  const dx = Math.max(C.l - x, 0, x - C.r);
  const dy = Math.max(C.t - y, 0, y - C.b);
  return Math.max(dx, dy);
}

function rayHitBox(ox, oz, dx, dz, o, pad) {
  // 在物件的局部座標（含旋轉）下做射線對 AABB
  const r = o.rot || 0, cr = Math.cos(r), sr = Math.sin(r);
  const px = ox - o.x, pz = oz - o.z;
  const org = [px * cr + pz * sr, -px * sr + pz * cr];
  const dir = [dx * cr + dz * sr, -dx * sr + dz * cr];
  const lo = [-o.w / 2 - pad, -o.d / 2 - pad];
  const hi = [o.w / 2 + pad, o.d / 2 + pad];
  let t0 = 0, t1 = COVER_RANGE;
  for (let k = 0; k < 2; k++) {
    if (Math.abs(dir[k]) < 1e-9) {
      if (org[k] < lo[k] || org[k] > hi[k]) return Infinity;
    } else {
      let a = (lo[k] - org[k]) / dir[k];
      let b = (hi[k] - org[k]) / dir[k];
      if (a > b) { const t = a; a = b; b = t; }
      t0 = Math.max(t0, a);
      t1 = Math.min(t1, b);
      if (t0 > t1) return Infinity;
    }
  }
  return t0;
}

function coverDist(angRad) {
  const fx = headX, fz = headZ;
  const rx = -headZ, rz = headX; // 右手邊（俯視，x 右、z 向後）
  const c = Math.cos(angRad), sn = Math.sin(angRad);
  const dx = fx * c + rx * sn, dz = fz * c + rz * sn;
  let best = COVER_RANGE;
  for (const o of obs) {
    if (o.h < 0.8 || o.dying) continue; // 太矮的不算掩體
    if (Math.hypot(o.x - pos.x, o.z - pos.z) > COVER_RANGE + Math.max(o.w, o.d) / 2 + 0.5) continue;
    const hit = rayHitBox(pos.x, pos.z, dx, dz, o, 0.3);
    if (hit < best) best = hit;
  }
  return best;
}

function coverProx(list) {
  let best = 0;
  for (const it of list) {
    const q = clamp01(1 - coverDist(it[0] * DEG) / COVER_RANGE);
    best = Math.max(best, it[1] * q * q * (3 - 2 * q));
  }
  return best;
}

function updateVision() {
  const tgt = { l: 1, r: 1, u: 1, d: 1 };
  if (running) {
    const m = clamp01(moveSpeed / 1.6);
    // 中央視野區依實際移動速度縮放：不動＝最大（×1.15），慢走中等，快走縮到約一半
    const speedMul = lerp(1.15, 0.5, Math.pow(clamp01(moveSpeed / 1.4), 0.6));
    const pr = coverProx([[40, 0.85], [90, 1], [140, 0.7]]);
    const pl = coverProx([[-40, 0.85], [-90, 1], [-140, 0.7]]);
    const pf = coverProx([[0, 1], [-20, 0.8], [20, 0.8]]);
    fov.move = m; fov.prox.l = pl; fov.prox.r = pr; fov.prox.f = pf;
    tgt.l = speedMul * (1 - SIDE_SHRINK * pl);
    tgt.r = speedMul * (1 - SIDE_SHRINK * pr);
    tgt.u = speedMul * (1 - FRONT_SHRINK * pf);
    tgt.d = tgt.u;
  } else {
    fov.move = 0; fov.prox.l = fov.prox.r = fov.prox.f = 0;
  }
  for (const k of ['l', 'r', 'u', 'd']) {
    const goal = Math.max(FOV_MIN, tgt[k] * susp.fovMul);
    fov[k] = lerp(fov[k], goal, goal < fov[k] ? FOV_IN : FOV_OUT);
  }
  C = centerRect();
}

// ==========================================================
// 視野：分析與呈現（與遊戲相同的規則）
// ==========================================================
function hash(a, b, c) {
  let x = Math.imul(a | 0, 73856093) ^ Math.imul(b | 0, 19349663) ^ Math.imul(c | 0, 83492791);
  x = Math.imul(x ^ (x >>> 13), 1274126177);
  x ^= x >>> 16;
  return (x >>> 0) / 4294967296;
}

function analyze() {
  smctx.drawImage(scene, 0, 0, AW, AH);
  const p = smctx.getImageData(0, 0, AW, AH).data;
  for (let k = 0; k < AW * AH; k++) gray[k] = 0.299 * p[4 * k] + 0.587 * p[4 * k + 1] + 0.114 * p[4 * k + 2];
  for (let j = 1; j < AH - 1; j++) {
    for (let i = 1; i < AW - 1; i++) {
      const k = j * AW + i;
      const gx = -gray[k - AW - 1] + gray[k - AW + 1] - 2 * gray[k - 1] + 2 * gray[k + 1] - gray[k + AW - 1] + gray[k + AW + 1];
      const gy = -gray[k - AW - 1] - 2 * gray[k - AW] - gray[k - AW + 1] + gray[k + AW - 1] + 2 * gray[k + AW] + gray[k + AW + 1];
      const m = Math.sqrt(gx * gx + gy * gy) / 4;
      edgeMag[k] = 0.6 * m + 0.4 * edgeMag[k];
    }
  }
}

function blit(x, y, w, h) {
  // 把場景畫布的一塊（CSS 像素座標）畫到主畫布同樣的位置
  if (w <= 0 || h <= 0) return;
  ctx.drawImage(scene, x * DPR, y * DPR, w * DPR, h * DPR, x, y, w, h);
}

function drawDots() {
  const thr = S.dotThreshold;
  const useCanny = cannyFresh();
  const buckets = [[], [], []];
  const ud = Math.min(1.3, Math.max(0.85, U * 1.4));
  const radii = [S.dotMin * ud, ((S.dotMin + S.dotMax) / 2) * ud, S.dotMax * ud];
  for (let j = 0; j < AH; j++) {
    for (let i = 0; i < AW; i++) {
      const k = j * AW + i;
      const x = i * SAMPLE + SAMPLE / 2, y = j * SAMPLE + SAMPLE / 2;
      const d = rectDist(x, y);
      if (d <= 0) continue;
      let edgeN = clamp01((edgeMag[k] - thr * 0.5) / (thr * 3.5));
      if (useCanny) {
        const ci = Math.min(DW - 1, (x / DS) | 0), cj = Math.min(DH - 1, (y / DS) | 0);
        let hit = 0;
        for (let b = -1; b <= 1 && !hit; b++) for (let a = -1; a <= 1; a++) { const cj2 = cj + b, ci2 = ci + a; if (cj2 >= 0 && ci2 >= 0 && cj2 < DH && ci2 < DW && cmask[cj2 * DW + ci2]) { hit = cmask[cj2 * DW + ci2]; break; } }
        edgeN = hit ? Math.max(edgeN, hit === 2 ? 0.85 : 0.55) : edgeN * 0.25;
      }
      const lumN = Math.pow(gray[k] / 255, 2.2) * 0.3;
      const v = Math.max(edgeN, lumN);
      if (v <= 0.02) continue;
      const prox = 0.3 + 0.7 * (1 - Math.min(1, d / (S.dotFalloff * U)));
      const n = Math.floor(v * prox * S.dotDensity * (S.limitOn ? scMul(x, y) : 1) + hash(i, j, 0));
      if (n <= 0) continue;
      const b = edgeN > 0.66 ? 2 : edgeN > 0.33 ? 1 : 0;
      for (let q = 0; q < n; q++) {
        buckets[b].push(x + (hash(i, j, q + 1) - 0.5) * SAMPLE, y + (hash(i, j, q + 11) - 0.5) * SAMPLE);
      }
    }
  }
  ctx.save();
  ctx.fillStyle = 'rgba(255,255,255,0.92)';
  for (let b = 0; b < 3; b++) {
    const pts = buckets[b], r = radii[b];
    ctx.beginPath();
    for (let q = 0; q < pts.length; q += 2) {
      ctx.moveTo(pts[q] + r, pts[q + 1]);
      ctx.arc(pts[q], pts[q + 1], r, 0, Math.PI * 2);
    }
    ctx.fill();
  }
  ctx.restore();
}

function drawBand() {
  for (let L = 0; L < S.bandCell.length; L++) {
    const s = S.bandCell[L] * U;
    const d0 = bandEdge[L], d1 = bandEdge[L + 1];
    const kx0 = Math.floor((0 - C.l) / s) - 1, kx1 = Math.ceil((W - C.l) / s) + 1;
    const ky0 = Math.floor((0 - C.t) / s) - 1, ky1 = Math.ceil((H - C.t) / s) + 1;
    for (let ky = ky0; ky <= ky1; ky++) {
      for (let kx = kx0; kx <= kx1; kx++) {
        const x0 = C.l + kx * s, y0 = C.t + ky * s;
        const cx = x0 + s / 2, cy = y0 + s / 2;
        if (cx < 0 || cx > W || cy < 0 || cy > H) continue;
        const d = rectDist(cx, cy);
        if (d <= d0 || d > d1) continue;
        const p = Math.pow(1 - d / BAND_TOTAL, S.bandPow);
        if (hash(kx, ky, L + 50) > p) continue;
        blit(x0, y0, s, s);
      }
    }
  }
}

function drawMarkers() {
  const thr = S.dotThreshold * 2.2;
  const R = 3;
  const cand = [];
  for (let j = R; j < AH - R; j++) {
    for (let i = R; i < AW - R; i++) {
      const m = edgeMag[j * AW + i];
      if (m < thr) continue;
      const x = i * SAMPLE + SAMPLE / 2, y = j * SAMPLE + SAMPLE / 2;
      if (rectDist(x, y) <= 0) continue;
      let isMax = true;
      for (let jj = -R; jj <= R && isMax; jj++) {
        for (let ii = -R; ii <= R; ii++) {
          if (edgeMag[(j + jj) * AW + i + ii] > m) { isMax = false; break; }
        }
      }
      if (isMax) cand.push({ x, y, m, i, j });
    }
  }
  cand.sort((p1, p2) => p2.m - p1.m);
  const n = Math.min(cand.length, S.markerCount);
  ctx.save();
  ctx.strokeStyle = 'rgba(255,255,255,0.9)';
  ctx.lineWidth = 1;
  for (let q = 0; q < n; q++) {
    const c = cand[q];
    const s = (8 + 6 * hash(c.i, c.j, 99)) * Math.max(0.85, U);
    ctx.strokeRect(Math.round(c.x - s / 2) + 0.5, Math.round(c.y - s / 2) + 0.5, s, s);
  }
  ctx.restore();
}

function composeLimited() {
  ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  ctx.fillStyle = '#000';
  ctx.fillRect(0, 0, W, H);
  analyze();
  drawDots();
  drawBand();
  blit(C.l, C.t, C.r - C.l, C.b - C.t);
  drawMarkers();
}

// ==========================================================
// 場景：鏡頭影像 + 虛擬建築（白色線條）
// ==========================================================
function drawVideo() {
  sctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  const vw = video.videoWidth, vh = video.videoHeight;
  if (vw && vh && video.readyState >= 2) {
    const s = Math.max(W / vw, H / vh);
    const dw = vw * s, dh = vh * s;
    sctx.drawImage(video, (W - dw) / 2, (H - dh) / 2, dw, dh);
    FPX = (s * (Math.max(vw, vh) / 2)) / Math.tan((S.fovLong * DEG) / 2);
  } else {
    sctx.fillStyle = '#1b1d22';
    sctx.fillRect(0, 0, W, H);
    FPX = (Math.max(W, H) / 2) / Math.tan((S.fovLong * DEG) / 2);
  }
}

function drawStructures(c) {
  const near = 0.15;
  const now = performance.now();
  c.lineJoin = 'round';
  for (const o of obs) {
    const dx = o.x - pos.x, dz = o.z - pos.z;
    const dist = Math.hypot(dx, dz);
    if (dist > 24) continue;
    const reach = Math.max(o.w, o.d);
    const cc = toCam(dx, -EYE, dz);
    if (cc[2] < -reach && dist > 3) continue;
    if (hiddenByRealWall(o)) continue;

    let gy = 1, gx = 1;
    if (o.gen || o.fade) {
      const t = clamp01((now - o.born) / (o.gen ? 2600 : 1200));
      const e = (u) => 1 - (1 - u) * (1 - u);
      gx = e(t);
      gy = e((t - 0.2) / 0.8);
      if (o.dying) { const k = 1 - clamp01((now - o.dying) / 900); gx *= k; gy *= k; }
      if (gy <= 0.01 && gx <= 0.01) continue;
    }
    const segs = dist < 9 ? o.segsNear : o.segsFar;
    const alpha = Math.max(0.35, 1 - dist / 24);
    c.strokeStyle = `rgba(255,255,255,${alpha.toFixed(2)})`;
    c.lineWidth = dist < 6 ? 2 : 1.4;
    const cr = Math.cos(o.rot || 0), sr = Math.sin(o.rot || 0);
    const ax = o.gAx === 9 ? 0 : (o.gAx || 0) * o.w / 2;
    const noX = o.gAx === 9;
    const tx = (x, z) => {
      const lx = noX ? x : ax + (x - ax) * gx;
      const lz = noX ? z : z * (o.gAx ? 1 : gx);
      return [lx * cr - lz * sr, lx * sr + lz * cr];
    };
    c.beginPath();
    for (let q = 0; q < segs.length; q++) {
      const sg = segs[q];
      const p1 = tx(sg[0], sg[2]), p2 = tx(sg[3], sg[5]);
      let a = toCam(dx + p1[0], sg[1] * gy - EYE, dz + p1[1]);
      let b = toCam(dx + p2[0], sg[4] * gy - EYE, dz + p2[1]);
      if (a[2] < near && b[2] < near) continue;
      if (a[2] < near) { const t = (near - a[2]) / (b[2] - a[2]); a = [lerp(a[0], b[0], t), lerp(a[1], b[1], t), near]; }
      else if (b[2] < near) { const t = (near - b[2]) / (a[2] - b[2]); b = [lerp(b[0], a[0], t), lerp(b[1], a[1], t), near]; }
      const pa = toScreen(a), pb = toScreen(b);
      c.moveTo(pa[0], pa[1]);
      c.lineTo(pb[0], pb[1]);
    }
    c.stroke();
  }
}

// ==========================================================
// 虛擬建築（單位：公尺）：用白色線條表示結構
// ==========================================================
let obs = [];

// 建築結構的線段（相對於中心）：外框、基座、樓板、柱、窗框
function buildSegs(w, d, h, kind, withWindows) {
  const segs = [];
  const hx = w / 2, hz = d / 2;
  const L = (x1, y1, z1, x2, y2, z2) => segs.push([x1, y1, z1, x2, y2, z2]);
  const rect = (y, ix) => {
    const ax = hx - (ix || 0), az = hz - (ix || 0);
    L(-ax, y, -az, ax, y, -az); L(ax, y, -az, ax, y, az);
    L(ax, y, az, -ax, y, az); L(-ax, y, az, -ax, y, -az);
  };
  rect(0); rect(h);
  L(-hx, 0, -hz, -hx, h, -hz); L(hx, 0, -hz, hx, h, -hz);
  L(hx, 0, hz, hx, h, hz); L(-hx, 0, hz, -hx, h, hz);

  if (kind === 'pillar') {
    rect(0.25, -0.05); rect(h - 0.3, -0.05);
    return segs;
  }
  if (kind === 'low') {
    rect(h - 0.06, 0.05); // 壓頂
    return segs;
  }

  // 牆：基座、樓板、柱、窗
  const plinth = 0.5;
  const ns = Math.max(1, Math.round((h - plinth) / 1.0));
  const storey = (h - plinth) / ns;
  rect(plinth);
  for (let i = 1; i < ns; i++) rect(plinth + i * storey);
  rect(h - 0.12);
  const longX = w >= d;
  const len = longX ? w : d;
  const nb = Math.max(1, Math.round(len / 1.4)); // 開間數
  const cols = [];
  for (let i = 0; i <= nb; i++) cols.push(-len / 2 + (i * len) / nb);
  for (const c0 of cols) {
    if (longX) { L(c0, 0, -hz, c0, h, -hz); L(c0, 0, hz, c0, h, hz); }
    else { L(-hx, 0, c0, -hx, h, c0); L(hx, 0, c0, hx, h, c0); }
  }
  if (withWindows) {
    for (let i = 0; i < nb; i++) {
      const a = cols[i] + 0.18, b = cols[i + 1] - 0.18;
      for (let s = 0; s < ns; s++) {
        const y0 = plinth + s * storey + 0.22, y1 = plinth + (s + 1) * storey - 0.22;
        for (const sd of [-1, 1]) {
          if (longX) {
            const z = sd * hz;
            L(a, y0, z, b, y0, z); L(b, y0, z, b, y1, z); L(b, y1, z, a, y1, z); L(a, y1, z, a, y0, z);
          } else {
            const x = sd * hx;
            L(x, y0, a, x, y0, b); L(x, y0, b, x, y1, b); L(x, y1, b, x, y1, a); L(x, y1, a, x, y0, a);
          }
        }
      }
    }
  }
  return segs;
}

function makeObs(x, z, w, d, h, kind, rot, gAx) {
  return {
    x, z, w, d, h, kind, rot: rot || 0, gAx: gAx || 0,
    gen: false, fade: false, gid: 0, born: 0, dying: 0,
    segsFar: buildSegs(w, d, h, kind, false),
    segsNear: buildSegs(w, d, h, kind, true),
  };
}

// ==========================================================
// 移動習慣 → 生成
// ==========================================================
const habit = { open: 0, hug: 0, fast: 0, still: 0, turn: 0, hx: 0, hz: 0 };
let genCount = 0, genGid = 0, genHistory = [];
let genLog = { text: '', until: 0 };
let nextGenAt = 0;
const MAX_GEN = 10;
const GEN_INTERVAL = 6000;
const GEN_FIRST = 8000;

function resetHabit() {
  habit.open = habit.hug = habit.fast = habit.still = habit.turn = 0;
  habit.hx = habit.hz = 0;
  genCount = 0; genGid = 0; genHistory = [];
  genLog = { text: '', until: 0 };
}

function updateHabit(dt) {
  const k = Math.min(1, dt / 10); // 約 10 秒的記憶
  const prox = Math.max(fov.prox.l, fov.prox.r);
  const moving = moveSpeed > 0.25;
  habit.open += ((prox < 0.12 ? 1 : 0) - habit.open) * k;
  habit.hug += ((prox > 0.45 ? 1 : 0) - habit.hug) * k;
  habit.still += ((moving ? 0 : 1) - habit.still) * k;
  habit.fast += ((moveSpeed > 1.3 ? 1 : 0) - habit.fast) * k;
  let dyaw = Math.atan2(headX, -headZ) - prevYaw;
  prevYaw = Math.atan2(headX, -headZ);
  if (dyaw > Math.PI) dyaw -= 2 * Math.PI;
  if (dyaw < -Math.PI) dyaw += 2 * Math.PI;
  habit.turn += (Math.max(-1, Math.min(1, dyaw * 12)) - habit.turn) * Math.min(1, dt / 5);
  if (moving) {
    habit.hx += (headX - habit.hx) * Math.min(1, dt * 1.2);
    habit.hz += (headZ - habit.hz) * Math.min(1, dt * 1.2);
  }
}

const GEN_INFO = {
  cover: { name: '掩體群', why: '你多在空曠處' },
  alley: { name: '巷弄', why: '你習慣貼牆走' },
  wall: { name: '長牆', why: '你走得很快' },
  room: { name: '小房間', why: '你常停下來' },
};

function roomSpecs(cx, cz, w, d, h, doors) {
  const T = 0.25, DW = 1.0, out = [];
  const hw = w / 2, hd = d / 2;
  for (const pr of [['n', cz - hd], ['s', cz + hd]]) {
    if (doors.includes(pr[0])) {
      const seg = (w - DW) / 2;
      out.push([cx - DW / 2 - seg / 2, pr[1], seg, T, h], [cx + DW / 2 + seg / 2, pr[1], seg, T, h]);
    } else out.push([cx, pr[1], w, T, h]);
  }
  const len = d - T;
  for (const pr of [['w', cx - hw], ['e', cx + hw]]) {
    if (doors.includes(pr[0])) {
      const seg = (len - DW) / 2;
      out.push([pr[1], cz - DW / 2 - seg / 2, T, seg, h], [pr[1], cz + DW / 2 + seg / 2, T, seg, h]);
    } else out.push([pr[1], cz, T, len, h]);
  }
  return out;
}

// ==========================================================
// 附著式生成：虛擬建築從「世界模型」裡的牆、柱、轉角長出來
//   規格 spec = [x, z, 長, 厚, 高, 種類, 旋轉角, 生長端]
//   旋轉角：局部 +x 軸在平面上的方向；生長端：-1 / +1 = 從該端沿長度長出，0 = 由中心，9 = 只往上長
//   房間 → 以轉角為一角，補上兩面牆（其中一面留門）
//   巷弄 → 平行於真牆、偏移 1.9 m、同長度的牆
//   長牆 → 從真牆的端點或既有虛擬牆的端點，沿方向延伸（或折 90°）
//   掩體 → 柱子往上長一層，周圍長出矮掩體；沒有柱時貼著牆長
// ==========================================================
function specObj(sp) { return { x: sp[0], z: sp[1], w: sp[2], d: sp[3], rot: sp[6] || 0 }; }

function toLocal(o, px, pz) {
  const r = o.rot || 0, c = Math.cos(r), s = Math.sin(r), dx = px - o.x, dz = pz - o.z;
  return [dx * c + dz * s, -dx * s + dz * c];
}
function distPointBox(px, pz, o) {
  const l = toLocal(o, px, pz);
  return Math.hypot(Math.max(Math.abs(l[0]) - o.w / 2, 0), Math.max(Math.abs(l[1]) - o.d / 2, 0));
}
function pts9(o) {
  const r = o.rot || 0, c = Math.cos(r), s = Math.sin(r), out = [];
  for (const a of [-1, 0, 1]) for (const b of [-1, 0, 1]) {
    const lx = (a * o.w) / 2, lz = (b * o.d) / 2;
    out.push([o.x + lx * c - lz * s, o.z + lx * s + lz * c]);
  }
  return out;
}
function boxesOverlap(a, b, pad) {
  for (const p of pts9(a)) if (distPointBox(p[0], p[1], b) < pad) return true;
  for (const p of pts9(b)) if (distPointBox(p[0], p[1], a) < pad) return true;
  return false;
}
function segCross(ax, az, bx, bz, cx, cz, dx, dz) {
  const d1x = bx - ax, d1z = bz - az, d2x = dx - cx, d2z = dz - cz;
  const den = d1x * d2z - d1z * d2x;
  if (Math.abs(den) < 1e-9) return false;
  const t = ((cx - ax) * d2z - (cz - az) * d2x) / den;
  const u = ((cx - ax) * d1z - (cz - az) * d1x) / den;
  return t > 0.02 && t < 0.98 && u > 0.02 && u < 0.98;
}

function wallSpec(x1, z1, x2, z2, h, T, kind) {
  return [(x1 + x2) / 2, (z1 + z2) / 2, Math.hypot(x2 - x1, z2 - z1), T || 0.25, h || 2.6, kind || 'wall', Math.atan2(z2 - z1, x2 - x1), -1];
}

function specsValid(specs, ign) {
  for (const sp of specs) {
    const o = specObj(sp);
    if (distPointBox(pos.x, pos.z, o) < 1.6) return false;
    for (const q of obs) if (!q.dying && boxesOverlap(o, q, 0.35)) return false;
    const long = o.w >= o.d, hl = (long ? o.w : o.d) / 2;
    const c = Math.cos(o.rot), s = Math.sin(o.rot);
    const ex = long ? c : -s, ez = long ? s : c;
    const ax = o.x - ex * hl, az = o.z - ez * hl, bx = o.x + ex * hl, bz = o.z + ez * hl;
    for (const w of world.walls) {
      if (w.hits < 2 || (ign && ign.has(w.id))) continue;
      if (segCross(ax, az, bx, bz, w.x1, w.z1, w.x2, w.z2)) return false;
    }
    for (const e of world.ents) {
      if (e.hits < 3 || (ign && ign.has(e.id))) continue;
      if (distPointBox(e.x, e.z, o) < 0.2) return false;
    }
  }
  return true;
}

// ---------- 候選錨點 ----------
function aScore(x, z, used) {
  const dx = x - pos.x, dz = z - pos.z, d = Math.hypot(dx, dz);
  const ang = Math.abs(wrapPi(Math.atan2(dx, -dz) - Math.atan2(headX, -headZ)));
  return Math.cos(Math.min(ang, Math.PI)) * 0.6 + 1 / (1 + d / 4) + rand(0, 0.3) - 0.5 * (used || 0) + (mkActiveNear(x, z, 4) ? 0.6 : 0);
}

function sideOf(w) { // 回傳 [單位法向量朝向使用者]
  const len = Math.hypot(w.x2 - w.x1, w.z2 - w.z1) || 1;
  const ux = (w.x2 - w.x1) / len, uz = (w.z2 - w.z1) / len;
  let nx = -uz, nz = ux;
  const mx = (w.x1 + w.x2) / 2, mz = (w.z1 + w.z2) / 2;
  if ((pos.x - mx) * nx + (pos.z - mz) * nz < 0) { nx = -nx; nz = -nz; }
  return { ux, uz, nx, nz, len, mx, mz };
}

function wallsNear(x, z, r) {
  const ids = new Set();
  for (const w of world.walls) {
    if (Math.hypot(w.x1 - x, w.z1 - z) < r || Math.hypot(w.x2 - x, w.z2 - z) < r) ids.add(w.id);
  }
  return ids;
}

function buildRoom(e) {
  const L = 3.0;
  let arms = e.dirs.slice();
  let u = null, v = null;
  if (arms.length >= 2) {
    let best = null;
    for (let i = 0; i < arms.length; i++) for (let j = i + 1; j < arms.length; j++) {
      const d = Math.abs(wrapPi(arms[i] - arms[j]));
      if (d > 50 * DEG && d < 130 * DEG && (!best || Math.abs(d - Math.PI / 2) < Math.abs(best[2] - Math.PI / 2))) best = [arms[i], arms[j], d];
    }
    if (best) { u = best[0]; v = best[1]; }
  }
  if (u === null && arms.length >= 1) {
    u = arms[0];
    const cand = [u + Math.PI / 2, u - Math.PI / 2];
    let pick = null;
    for (const a of cand) {
      const px = e.x + (Math.cos(u) + Math.cos(a)) * L * 0.5, pz = e.z + (Math.sin(u) + Math.sin(a)) * L * 0.5;
      if (isFree(px, pz)) { pick = a; break; }
    }
    if (pick === null) return null;
    v = pick;
  }
  if (u === null) return null;
  const ux = Math.cos(u), uz = Math.sin(u), vx = Math.cos(v), vz = Math.sin(v);
  let freeN = 0;
  for (const f of [0.35, 0.5, 0.65]) if (isFree(e.x + (ux + vx) * L * f, e.z + (uz + vz) * L * f)) freeN++;
  if (!freeN) return null;
  const P1 = [e.x + ux * L, e.z + uz * L], P2 = [P1[0] + vx * L, P1[1] + vz * L];
  const Q1 = [e.x + vx * L, e.z + vz * L];
  const h1 = L / 2 - 0.5;
  const specs = [
    wallSpec(P1[0], P1[1], P2[0], P2[1]),
    wallSpec(Q1[0], Q1[1], Q1[0] + ux * h1, Q1[1] + uz * h1),
    wallSpec(P2[0], P2[1], P2[0] - ux * h1, P2[1] - uz * h1),
  ];
  const ign = wallsNear(e.x, e.z, 0.7); ign.add(e.id);
  return { specs, ign, label: '小房間・以轉角為一角' };
}

function buildAlley(w) {
  const s = sideOf(w);
  const Ln = Math.min(s.len, 5.5);
  const specs = [[s.mx + s.nx * 1.9, s.mz + s.nz * 1.9, Ln, 0.25, 2.6, 'wall', Math.atan2(s.uz, s.ux), -1]];
  const ign = new Set([w.id]);
  return { specs, ign, label: '巷弄・平行於真牆' };
}

function buildExtend(a) {
  // a: {x,z,dx,dz}（端點與向外的單位方向）
  const L = 2.6;
  let dx = a.dx, dz = a.dz, label = '長牆・沿牆延伸';
  if (Math.random() < 0.4) {
    const nx = -dz, nz = dx;
    const side = ((pos.x - a.x) * nx + (pos.z - a.z) * nz) >= 0 ? 1 : -1;
    dx = nx * side; dz = nz * side;
    label = '長牆・在端點轉折';
  }
  const specs = [wallSpec(a.x, a.z, a.x + dx * L, a.z + dz * L)];
  return { specs, ign: wallsNear(a.x, a.z, 0.7), label };
}

function buildCoverCol(e) {
  const cw = Math.max(0.3, e.w);
  const specs = [[e.x, e.z, cw, cw, 3.0, 'pillar', 0, 9]];
  const base = Math.atan2(pos.z - e.z, pos.x - e.x);
  for (const off of [0.9, -0.9]) {
    const a = base + off;
    specs.push([e.x + Math.cos(a) * 1.3, e.z + Math.sin(a) * 1.3, 0.9, 0.9, 1.05, 'low', a + Math.PI / 2, 0]);
  }
  return { specs, ign: new Set([e.id]), label: '掩體群・柱子往上長一層' };
}

function buildCoverObj(o) {
  const base = Math.atan2(pos.z - o.z, pos.x - o.x);
  const specs = [];
  for (const off of [0.7, -0.7]) {
    const a = base + off;
    specs.push([o.x + Math.cos(a) * 1.2, o.z + Math.sin(a) * 1.2, 0.9, 0.6, 1.05, 'low', a + Math.PI / 2, 0]);
  }
  return { specs, ign: new Set(), label: `掩體群・以真實的${o.zh}為錨點` };
}

function buildCoverWall(w) {
  const s = sideOf(w);
  const specs = [];
  for (const t of [0.3, 0.7]) {
    specs.push([w.x1 + (w.x2 - w.x1) * t + s.nx * 0.65, w.z1 + (w.z2 - w.z1) * t + s.nz * 0.65, 1.2, 0.6, 1.05, 'low', Math.atan2(s.uz, s.ux), 0]);
  }
  return { specs, ign: new Set([w.id]), label: '掩體群・貼著真牆' };
}

function candidates(type) {
  const out = [];
  const okd = (x, z) => { const d = Math.hypot(x - pos.x, z - pos.z); return d >= 1.8 && d <= 11; };
  const ents = world.ents.filter((e) => e.hits >= 3 && e.used < 3 && okd(e.x, e.z));
  const walls = world.walls.filter((w) => w.hits >= 2 && w.used < 2 && Math.hypot(w.x2 - w.x1, w.z2 - w.z1) >= 1.2 && okd((w.x1 + w.x2) / 2, (w.z1 + w.z2) / 2));
  if (type === 'room') {
    for (const e of ents) if (e.type === 'corner') out.push({ ref: e, s: aScore(e.x, e.z, e.used), build: () => buildRoom(e) });
  } else if (type === 'alley') {
    for (const w of walls) out.push({ ref: w, s: aScore((w.x1 + w.x2) / 2, (w.z1 + w.z2) / 2, w.used), build: () => buildAlley(w) });
  } else if (type === 'wall') {
    for (const w of world.walls) {
      if (w.hits < 2 || w.used >= 3) continue;
      const len = Math.hypot(w.x2 - w.x1, w.z2 - w.z1);
      if (len < 1.2) continue;
      const ux = (w.x2 - w.x1) / len, uz = (w.z2 - w.z1) / len;
      for (const sg of [1, -1]) {
        const x = sg > 0 ? w.x2 : w.x1, z = sg > 0 ? w.z2 : w.z1;
        if (!okd(x, z)) continue;
        out.push({ ref: w, s: aScore(x, z, w.used), build: () => buildExtend({ x, z, dx: ux * sg, dz: uz * sg }) });
      }
    }
    for (const o of obs) {
      if (!o.gen || o.dying || o.kind !== 'wall' || o.grown) continue;
      const c = Math.cos(o.rot || 0), s = Math.sin(o.rot || 0);
      for (const sg of [1, -1]) {
        const x = o.x + c * sg * o.w / 2, z = o.z + s * sg * o.w / 2;
        if (!okd(x, z)) continue;
        out.push({ ref: o, s: aScore(x, z, 0) - 0.15, build: () => buildExtend({ x, z, dx: c * sg, dz: s * sg }) });
      }
    }
  } else if (type === 'cover') {
    for (const o of omem) {
      if (o.hits >= 3 && o.role === 'cover' && o.used < 2 && okd(o.x, o.z)) out.push({ ref: o, s: aScore(o.x, o.z, o.used) + 0.1, build: () => buildCoverObj(o) });
    }
    for (const e of ents) if (e.type === 'column') out.push({ ref: e, s: aScore(e.x, e.z, e.used) + 0.2, build: () => buildCoverCol(e) });
    for (const w of walls) out.push({ ref: w, s: aScore((w.x1 + w.x2) / 2, (w.z1 + w.z2) / 2, w.used) - 0.2, build: () => buildCoverWall(w) });
  }
  out.sort((p, q) => q.s - p.s);
  return out;
}

function tryAttach(type) {
  const list = candidates(type);
  for (let k = 0; k < Math.min(8, list.length); k++) {
    const c = list[k], b = c.build();
    if (!b || !specsValid(b.specs, b.ign)) continue;
    genGid++;
    const now = performance.now();
    for (const sp of b.specs) {
      const o = makeObs(sp[0], sp[1], sp[2], sp[3], sp[4], sp[5], sp[6], sp[7]);
      o.gen = true; o.gid = genGid; o.born = now;
      obs.push(o);
    }
    if (c.ref.used !== undefined) c.ref.used++;
    else c.ref.grown = true;
    genLabel = b.label;
    return true;
  }
  return false;
}
let genLabel = '';

// 沒有偵測資料時的舊作法（自由生成，僅供桌機／無鏡頭測試）
function genSpecs(type, cx, cz, alongX) {
  const loc = [];
  if (type === 'room') {
    return roomSpecs(cx, cz, 3.6, 3.6, 2.6, alongX ? 'ew' : 'ns').map((s) => [s[0], s[1], s[2], s[3], s[4], 'wall', 0, 0]);
  }
  if (type === 'cover') {
    loc.push([-1.1, -0.8, 0.9, 0.9, 1.05, 'low'], [0.9, -0.9, 0.9, 0.9, 1.15, 'low'],
      [-0.8, 1.0, 0.9, 0.9, 1.0, 'low'], [1.2, 0.8, 0.9, 0.9, 0.95, 'low'], [0, 0, 0.4, 0.4, 2.6, 'pillar']);
  } else if (type === 'alley') {
    loc.push([0, -0.925, 5, 0.25, 2.6, 'wall'], [0, 0.925, 5, 0.25, 2.6, 'wall']);
  } else if (type === 'wall') {
    loc.push([-1.7, 0, 2.2, 0.25, 2.6, 'wall'], [1.7, 0, 2.2, 0.25, 2.6, 'wall']);
  }
  return loc.map((q) => (alongX
    ? [cx + q[0], cz + q[1], q[2], q[3], q[4], q[5], 0, 0]
    : [cx + q[1], cz + q[0], q[3], q[2], q[4], q[5], 0, 0]));
}

function tryPlaceFree(type) {
  let hx = habit.hx, hz = habit.hz;
  let len = Math.hypot(hx, hz);
  if (len < 0.25) { hx = headX; hz = headZ; len = 1; }
  hx /= len; hz /= len;
  const a = habit.turn * 0.5;
  const dirx = hx * Math.cos(a) - hz * Math.sin(a);
  const dirz = hx * Math.sin(a) + hz * Math.cos(a);
  const alongHeading = Math.abs(hx) > Math.abs(hz);
  for (let k = 0; k < 30; k++) {
    const spread = (k / 30) * Math.PI * 0.9;
    const ta = rand(-spread, spread);
    const far = 3.6 + rand(0, 2.2 + k * 0.12);
    const ux = dirx * Math.cos(ta) - dirz * Math.sin(ta);
    const uz = dirx * Math.sin(ta) + dirz * Math.cos(ta);
    const cx = pos.x + ux * far + rand(-0.4, 0.4);
    const cz = pos.z + uz * far + rand(-0.4, 0.4);
    let alongX;
    if (type === 'alley') alongX = alongHeading;
    else if (type === 'wall') alongX = !alongHeading;
    else if (type === 'room') alongX = alongHeading;
    else alongX = Math.random() < 0.5;
    const specs = genSpecs(type, cx, cz, alongX);
    if (!specsValid(specs, null)) continue;
    genGid++;
    const now = performance.now();
    for (const sp of specs) {
      const o = makeObs(sp[0], sp[1], sp[2], sp[3], sp[4], sp[5], 0, 0);
      o.gen = true; o.gid = genGid; o.born = now;
      obs.push(o);
    }
    genLabel = '自由生成（未附著）';
    return true;
  }
  return false;
}

function tryPlace(type) { return S.freeGen ? tryPlaceFree(type) : tryAttach(type); }

function generateByHabit() {
  const scores = {
    cover: habit.open + 0.12,
    alley: habit.hug * 1.2 + 0.05,
    wall: habit.fast * 1.2 + 0.05,
    room: habit.still + 0.1,
  };
  const recent = genHistory.slice(-3);
  const order = Object.keys(scores)
    .map((k) => ({ k, v: scores[k] - 0.2 * recent.filter((r) => r === k).length + rand(0, 0.12) }))
    .sort((p1, p2) => p2.v - p1.v);
  for (const it of order) {
    if (tryPlace(it.k)) {
      genCount++;
      genHistory.push(it.k);
      const info = GEN_INFO[it.k];
      genLog = { text: `生成 #${genCount}：${info.name}（${info.why}）→ ${genLabel}`, until: performance.now() + 6000 };
      pruneOldGen();
      return true;
    }
  }
  return false;
}

function pruneOldGen() {
  const alive = {};
  for (const o of obs) if (o.gen && !o.dying) (alive[o.gid] = alive[o.gid] || []).push(o);
  const ids = Object.keys(alive).map(Number).sort((p1, p2) => p1 - p2);
  const now = performance.now();
  for (const id of ids) {
    if (ids.length <= MAX_GEN) break;
    const far = alive[id].every((o) => Math.hypot(o.x - pos.x, o.z - pos.z) > 10);
    if (!far) continue;
    for (const o of alive[id]) o.dying = now;
    ids.splice(ids.indexOf(id), 1);
  }
}

function updateGeneration(now) {
  if (obs.some((o) => o.dying && now - o.dying > 900)) obs = obs.filter((o) => !(o.dying && now - o.dying > 900));
  if (now >= nextGenAt) {
    const ok = generateByHabit();
    nextGenAt = now + (ok ? GEN_INTERVAL : 1800);
  }
}

// ==========================================================
// 空間偵測（單眼、啟發式）
//   1. 特徵點：Harris 角點
//   2. 線條：以「重力方向」為前提的垂直線偵測（把邊緣像素依方位角投票，
//      同一條鉛直線上的像素方位角相同）
//   3. 地板測距：垂直線的底端落在地面 → 用相機高度與俯仰角算出距離
//   4. 語義分割（近似）：地板（顏色種子 + 區域生長）／牆／天花板
//   5. 分類：柱（成對的窄垂直線）、轉角（左右兩側地牆交線方向不同）、牆邊
//   6. 世界模型：把偵測結果融合成公尺座標的實體，跨影格累積、衰減
// 沒有 LiDAR：iOS Safari 沒有深度 API；Android 的 WebXR 深度另開 session，
// 無法與這條相機管線並用，所以這裡只做能力檢查並標示。
// ==========================================================
const DS = 4; // 偵測用取樣格（像素）
let DW = 0, DH = 0;
const dm = document.createElement('canvas');
const dmctx = dm.getContext('2d', { willReadFrequently: true });
const segCv = document.createElement('canvas');
const segCtx = segCv.getContext('2d');
let dgray = new Float32Array(1), dgx = new Float32Array(1), dgy = new Float32Array(1), dmag = new Float32Array(1);
let dR = new Float32Array(1), dlab = new Uint8Array(1), dqueue = new Int32Array(1), dpx = null;
let segImg = null;

const det = {
  feats: [], vlines: [], ms: 0, passes: 0, skipped: 0,
  floorSeed: null, floorPct: 0, wallPct: 0, ceilPct: 0,
  depth: '檢查中…', lastRun: 0, thr: 12,
};
const world = { ents: [], walls: [], free: new Map(), nid: 1, pass: 0 };
let angSpeed = 0; // 視線角速度（弧度/秒）
let prevF = null;

function detectResize() {
  DW = Math.ceil(W / DS);
  DH = Math.ceil(H / DS);
  dm.width = DW; dm.height = DH;
  segCv.width = DW; segCv.height = DH;
  const n = DW * DH;
  dgray = new Float32Array(n); dgx = new Float32Array(n); dgy = new Float32Array(n);
  dmag = new Float32Array(n); dR = new Float32Array(n);
  dlab = new Uint8Array(n); dqueue = new Int32Array(n);
  segImg = segCtx.createImageData(DW, DH);
  cannyResize();
}

// 螢幕像素 → 世界方向（遊戲座標：x 右、y 上、z 朝後）
function rayW(px, py) {
  const cx = (px - W / 2) / FPX, cy = -(py - H / 2) / FPX;
  return [
    cx * B.sr[0] + cy * B.su[0] + B.F[0],
    cx * B.sr[1] + cy * B.su[1] + B.F[1],
    cx * B.sr[2] + cy * B.su[2] + B.F[2],
  ];
}
function rayY(px, py) { return ((px - W / 2) / FPX) * B.sr[1] - ((py - H / 2) / FPX) * B.su[1] + B.F[1]; }
// 螢幕像素打到地面（眼高 EYE）的位置
function floorPoint(px, py) {
  const r = rayW(px, py);
  if (r[1] > -0.035) return null;
  const t = EYE / -r[1];
  return { x: pos.x + r[0] * t, z: pos.z + r[2] * t, d: Math.hypot(r[0], r[2]) * t };
}
// 該像素處「世界鉛直方向」在螢幕上的單位向量
function vertDir(px, py) {
  const cx = (px - W / 2) / FPX, cy = -(py - H / 2) / FPX;
  const u0 = B.sr[1], u1 = B.su[1], u2 = B.F[1];
  let sx = FPX * (u0 - cx * u2), sy = -FPX * (u1 - cy * u2);
  const l = Math.hypot(sx, sy) || 1;
  return [sx / l, sy / l];
}

function trackAng(dt) {
  if (prevF) {
    const d = Math.max(-1, Math.min(1, dot3(prevF, B.F)));
    angSpeed += (Math.acos(d) / Math.max(dt, 1e-3) - angSpeed) * Math.min(1, dt * 8);
  }
  prevF = [B.F[0], B.F[1], B.F[2]];
}

// ---------- 1. 梯度與特徵點 ----------
function detGradients() {
  dpx = dmctx.getImageData(0, 0, DW, DH).data;
  const n = DW * DH;
  for (let k = 0; k < n; k++) dgray[k] = 0.299 * dpx[4 * k] + 0.587 * dpx[4 * k + 1] + 0.114 * dpx[4 * k + 2];
  for (let j = 1; j < DH - 1; j++) {
    for (let i = 1; i < DW - 1; i++) {
      const k = j * DW + i;
      const gx = (-dgray[k - DW - 1] + dgray[k - DW + 1] - 2 * dgray[k - 1] + 2 * dgray[k + 1] - dgray[k + DW - 1] + dgray[k + DW + 1]) / 4;
      const gy = (-dgray[k - DW - 1] - 2 * dgray[k - DW] - dgray[k - DW + 1] + dgray[k + DW - 1] + 2 * dgray[k + DW] + dgray[k + DW + 1]) / 4;
      dgx[k] = gx; dgy[k] = gy; dmag[k] = Math.sqrt(gx * gx + gy * gy);
    }
  }
}

function detHarris() {
  let mx = 0;
  for (let j = 2; j < DH - 2; j++) {
    for (let i = 2; i < DW - 2; i++) {
      let sxx = 0, syy = 0, sxy = 0;
      for (let b = -1; b <= 1; b++) {
        for (let a = -1; a <= 1; a++) {
          const k = (j + b) * DW + i + a;
          const ix = dgx[k], iy = dgy[k];
          sxx += ix * ix; syy += iy * iy; sxy += ix * iy;
        }
      }
      const r = sxx * syy - sxy * sxy - 0.05 * (sxx + syy) * (sxx + syy);
      dR[j * DW + i] = r;
      if (r > mx) mx = r;
    }
  }
  const thr = Math.max(mx * 0.06, 1);
  const out = [];
  for (let j = 3; j < DH - 3; j++) {
    for (let i = 3; i < DW - 3; i++) {
      const k = j * DW + i, r = dR[k];
      if (r < thr) continue;
      let ok = true;
      for (let b = -2; b <= 2 && ok; b++) for (let a = -2; a <= 2; a++) if ((a || b) && dR[k + b * DW + a] > r) { ok = false; break; }
      if (ok) out.push({ i, j, r });
    }
  }
  out.sort((p, q) => q.r - p.r);
  det.feats = out.slice(0, 90);
  det.harrisMax = mx;
}

// ---------- 2. 垂直線（依方位角投票） ----------
function detVertical(thr) {
  const NB = 720;
  const votes = new Float32Array(NB);
  const cb = [], ck = [];
  // 混合：Canny 細邊緣決定「線在哪個方位」（投票），Sobel 強邊緣只用來補完線的長度（角落處 Canny 常中斷）
  for (let j = 1; j < DH - 1; j++) {
    for (let i = 1; i < DW - 1; i++) {
      const k = j * DW + i, m = dmag[k];
      const isCanny = S.cannyOn ? cmask[k] > 0 && m >= 1 : m >= thr;
      if (!isCanny && !(S.cannyOn && m >= thr)) continue;
      const px = (i + 0.5) * DS, py = (j + 0.5) * DS;
      const vv = vertDir(px, py);
      const tx = -dgy[k] / m, ty = dgx[k] / m;
      if (Math.abs(tx * vv[0] + ty * vv[1]) < 0.965) continue;
      const r = rayW(px, py);
      const az = Math.atan2(r[0], -r[2]);
      const bin = Math.min(NB - 1, Math.floor(((az + Math.PI) / (2 * Math.PI)) * NB));
      if (isCanny) votes[bin]++;
      cb.push(bin); ck.push(k);
    }
  }
  const sv = new Float32Array(NB);
  for (let b = 0; b < NB; b++) sv[b] = votes[(b + NB - 1) % NB] + votes[b] + votes[(b + 1) % NB];
  const minV = Math.max(14, 0.08 * DH);
  const peaks = [];
  for (let b = 0; b < NB; b++) {
    if (sv[b] < minV) continue;
    let top = true;
    for (let q = -3; q <= 3; q++) if (sv[(b + q + NB) % NB] > sv[b] || (q < 0 && sv[(b + q + NB) % NB] === sv[b])) { top = false; break; }
    if (top) peaks.push(b);
  }
  const lines = [];
  for (const pb of peaks) {
    const rowN = new Uint16Array(DH), rowX = new Float32Array(DH);
    for (let q = 0; q < cb.length; q++) {
      const d = Math.abs(((cb[q] - pb + NB + NB / 2) % NB) - NB / 2);
      if (d > 1) continue;
      const k = ck[q], j = (k / DW) | 0, i = k - j * DW;
      rowN[j]++; rowX[j] += i;
    }
    let best = null, start = -1, last = -9;
    const consider = () => { if (start >= 0 && (!best || last - start > best[1] - best[0])) best = [start, last]; };
    for (let j = 0; j < DH; j++) {
      if (!rowN[j]) continue;
      if (start < 0 || j - last > 3) { consider(); start = j; }
      last = j;
    }
    consider();
    if (!best) continue;
    const jt = best[0], jb = best[1];
    if (jb - jt < Math.max(14, 0.08 * DH)) continue;
    const avgX = (j0, j1) => {
      let s = 0, n = 0;
      for (let j = j0; j <= j1; j++) if (rowN[j]) { s += rowX[j]; n += rowN[j]; }
      return n ? (s / n + 0.5) * DS : null;
    };
    const xb = avgX(Math.max(jt, jb - 4), jb), xt = avgX(jt, Math.min(jb, jt + 4));
    if (xb == null || xt == null) continue;
    const yb = (jb + 1) * DS, yt = jt * DS;
    const ib = Math.round(xb / DS), clipped = jb >= DH - 5;
    const az = ((pb + 0.5) / NB) * 2 * Math.PI - Math.PI;
    const fp = clipped ? null : floorPoint(xb, yb);
    lines.push({ xb, yb, xt, yt, ib, jb, jt, az, fp, clipped, kind: 'line' });
  }
  det.vlines = lines;
  return lines;
}

// ---------- 3. 底端兩側的地牆交線（分辨轉角） ----------
function junctionSide(ib, jb, sgn, thr) {
  const vv = vertDir(ib * DS, jb * DS);
  let C = 0, S2 = 0, Wt = 0, n = 0;
  for (let j = Math.max(1, jb - 7); j <= Math.min(DH - 2, jb + 5); j++) {
    for (let s = 3; s <= 18; s++) {
      const i = ib + sgn * s;
      if (i < 1 || i >= DW - 1) break;
      const k = j * DW + i, m = dmag[k];
      if (S.cannyOn ? !cmask[k] || m < 1 : m < thr) continue;
      const tx = -dgy[k] / m, ty = dgx[k] / m;
      if (Math.abs(tx * vv[0] + ty * vv[1]) > 0.85) continue;
      const phi = Math.atan2(ty, tx);
      C += m * Math.cos(2 * phi); S2 += m * Math.sin(2 * phi); Wt += m; n++;
    }
  }
  if (n < 6) return null;
  if (Math.hypot(C, S2) / Wt < 0.55) return null;
  const phi = 0.5 * Math.atan2(S2, C);
  if (Math.abs(Math.cos(phi)) < 0.25) return null;
  return { phi, n };
}

function marchLine(i0, j0, dx, dy, thr) {
  // 邊緣追蹤：沿主軸前進，每步在垂直方向 ±2 格內找最強邊緣並微調位置
  const alongX = Math.abs(dx) >= Math.abs(dy);
  const step = alongX ? Math.sign(dx) : Math.sign(dy);
  const slope = alongX ? dy / dx : dx / dy;
  let x = i0, y = j0, miss = 0, gx = x, gy = y;
  for (let s = 0; s < DW * 2; s++) {
    if (alongX) { x += step; y += slope * step; } else { y += step; x += slope * step; }
    const ii = Math.round(x), jj = Math.round(y);
    if (ii < 3 || ii >= DW - 3 || jj < 3 || jj >= DH - 3) break;
    let bm = 0, bo = 0;
    for (let o = -2; o <= 2; o++) {
      const kk = alongX ? (jj + o) * DW + ii : jj * DW + ii + o;
      const m = S.cannyOn ? (cmask[kk] ? dmag[kk] + 1 : 0) : dmag[kk];
      if (m > bm) { bm = m; bo = o; }
    }
    if (S.cannyOn ? bm > 0 : bm >= thr * 0.6) {
      miss = 0;
      if (alongX) y += bo * 0.35; else x += bo * 0.35;
      gx = x; gy = y;
    } else if (++miss > 4) break;
  }
  return [gx, gy];
}

function harrisNear(i, j) {
  let m = 0;
  for (let b = -3; b <= 3; b++) for (let a = -3; a <= 3; a++) {
    const ii = i + a, jj = j + b;
    if (ii < 2 || jj < 2 || ii >= DW - 2 || jj >= DH - 2) continue;
    if (dR[jj * DW + ii] > m) m = dR[jj * DW + ii];
  }
  return m > (det.harrisMax || 1) * 0.06;
}

function wrapPi(a) { while (a > Math.PI) a -= 2 * Math.PI; while (a < -Math.PI) a += 2 * Math.PI; return a; }

function classifyLines(lines, thr) {
  const obsE = [], obsW = [];
  det.sides = [];
  const ranged = lines.filter((l) => l.fp && l.fp.d >= 0.6 && l.fp.d <= 10);
  const used = new Set();
  // 柱：兩條接近的垂直線，底端距離相近，間距換算成寬度 0.1–0.9 m
  for (let a = 0; a < ranged.length; a++) {
    for (let b = a + 1; b < ranged.length; b++) {
      if (used.has(a) || used.has(b)) continue;
      const A = ranged[a], Bn = ranged[b];
      const da = Math.abs(wrapPi(A.az - Bn.az));
      const r = (A.fp.d + Bn.fp.d) / 2;
      const wd = r * da;
      if (wd < 0.1 || wd > 0.9 || Math.abs(A.fp.d - Bn.fp.d) > 0.45) continue;
      used.add(a); used.add(b);
      obsE.push({ type: 'column', x: (A.fp.x + Bn.fp.x) / 2, z: (A.fp.z + Bn.fp.z) / 2, w: wd, dirs: [] });
    }
  }
  // 其餘：轉角或牆邊，並沿交線追出牆段
  ranged.forEach((L, idx) => {
    if (used.has(idx)) return;
    const jb = Math.min(DH - 2, L.jb + 1);
    const sides = [-1, 1].map((sg) => {
      const js = junctionSide(L.ib, jb, sg, thr);
      if (!js) return null;
      let dx = Math.cos(js.phi), dy = Math.sin(js.phi);
      if (sg * dx < 0) { dx = -dx; dy = -dy; }
      const e = marchLine(L.ib, jb, dx, dy, thr);
      const fe = floorPoint((e[0] + 0.5) * DS, (e[1] + 0.5) * DS);
      return { sg, phi: js.phi, end: fe };
    });
    det.sides.push({ ib: L.ib, jb, sides: sides.map((q) => q && { sg: q.sg, phi: +(q.phi / DEG).toFixed(1), end: q.end && { x: +q.end.x.toFixed(2), z: +q.end.z.toFixed(2) } }) });
    let type = 'edge';
    const dirs = [];
    const [sl, sr] = sides;
    if (sl && sr) {
      let dphi = Math.abs(sl.phi - sr.phi) % Math.PI;
      dphi = Math.min(dphi, Math.PI - dphi);
      if (dphi > 14 * DEG || (dphi > 8 * DEG && harrisNear(L.ib, jb))) type = 'corner';
    }
    for (const sd of sides) {
      if (!sd || !sd.end) continue;
      const len = Math.hypot(sd.end.x - L.fp.x, sd.end.z - L.fp.z);
      if (len < 0.8 || len > 12) continue;
      dirs.push(Math.atan2(sd.end.z - L.fp.z, sd.end.x - L.fp.x));
      obsW.push({ x1: L.fp.x, z1: L.fp.z, x2: sd.end.x, z2: sd.end.z });
    }
    obsE.push({ type, x: L.fp.x, z: L.fp.z, w: 0.2, dirs });
  });
  return { obsE, obsW };
}

// ---------- 4. 語義分割（近似） ----------
function detSegment(thr, now) {
  const n = DW * DH;
  dlab.fill(0);
  // 地板顏色種子：畫面下方中央、低紋理、射線朝下；用 2-means 容許兩種色調（如棋盤格地磚）
  const smp = [];
  for (let j = Math.floor(DH * 0.88); j < DH - 1; j++) {
    for (let i = Math.floor(DW * 0.3); i < Math.floor(DW * 0.7); i++) {
      const k = j * DW + i;
      if (dmag[k] > thr * 2) continue;
      if (rayY((i + 0.5) * DS, (j + 0.5) * DS) > -0.15) continue;
      smp.push([dpx[4 * k], dpx[4 * k + 1], dpx[4 * k + 2]]);
    }
  }
  if (smp.length > 20) {
    let lo = smp[0], hi = smp[0];
    const lum = (c) => c[0] + c[1] + c[2];
    for (const c of smp) { if (lum(c) < lum(lo)) lo = c; if (lum(c) > lum(hi)) hi = c; }
    let cs = [lo.slice(), hi.slice()];
    for (let it = 0; it < 3; it++) {
      const acc = [[0, 0, 0, 0], [0, 0, 0, 0]];
      for (const c of smp) {
        const d0 = Math.abs(c[0] - cs[0][0]) + Math.abs(c[1] - cs[0][1]) + Math.abs(c[2] - cs[0][2]);
        const d1 = Math.abs(c[0] - cs[1][0]) + Math.abs(c[1] - cs[1][1]) + Math.abs(c[2] - cs[1][2]);
        const q = d0 <= d1 ? 0 : 1;
        acc[q][0] += c[0]; acc[q][1] += c[1]; acc[q][2] += c[2]; acc[q][3]++;
      }
      for (let q = 0; q < 2; q++) if (acc[q][3] > 5) cs[q] = [acc[q][0] / acc[q][3], acc[q][1] / acc[q][3], acc[q][2] / acc[q][3]];
    }
    det.floorSeed = det.floorSeed ? cs.map((c, q) => c.map((v, m) => v + (det.floorSeed[q][m] - v) * 0.6)) : cs;
  }
  const seed = det.floorSeed;
  const floorLike = new Uint8Array(n);
  const ceilLike = new Uint8Array(n);
  for (let j = 1; j < DH - 1; j++) {
    for (let i = 1; i < DW - 1; i++) {
      const k = j * DW + i;
      const ry = rayY((i + 0.5) * DS, (j + 0.5) * DS);
      const flat = dmag[k] < thr * 1.6;
      if (ry < -0.03 && seed) {
        let dc = 9999;
        for (const sc of seed) dc = Math.min(dc, Math.abs(dpx[4 * k] - sc[0]) + Math.abs(dpx[4 * k + 1] - sc[1]) + Math.abs(dpx[4 * k + 2] - sc[2]));
        if (dc < 75 && dmag[k] < thr * 3) floorLike[k] = 1;
      } else if (ry > 0.5 && flat) ceilLike[k] = 1;
    }
  }
  // 從下緣種子區域生長
  let qh = 0, qt = 0;
  for (let j = Math.floor(DH * 0.88); j < DH - 1; j++) {
    for (let i = 1; i < DW - 1; i++) {
      const k = j * DW + i;
      if (floorLike[k] && !dlab[k]) { dlab[k] = 1; dqueue[qt++] = k; }
    }
  }
  while (qh < qt) {
    const k = dqueue[qh++];
    const i = k % DW;
    for (const nb of [k - 1, k + 1, k - DW, k + DW]) {
      if (nb < 0 || nb >= n) continue;
      if ((nb === k - 1 && i === 0) || (nb === k + 1 && i === DW - 1)) continue;
      if (floorLike[nb] && !dlab[nb]) { dlab[nb] = 1; dqueue[qt++] = nb; }
    }
  }
  // 世界模型回饋：地板點若在使用者與它之間隔著已知的牆，就不是地板（避免牆面被當成地板）
  const solid = world.walls.filter((w) => w.hits >= 2);
  if (solid.length) {
    for (let j = 1; j < DH - 1; j += 1) {
      for (let i = 1; i < DW - 1; i += 1) {
        const k = j * DW + i;
        if (dlab[k] !== 1) continue;
        const fp = floorPoint((i + 0.5) * DS, (j + 0.5) * DS);
        if (!fp) continue;
        for (const w of solid) {
          if (segCrossAny(pos.x, pos.z, fp.x, fp.z, w.x1, w.z1, w.x2, w.z2)) { dlab[k] = 2; break; }
        }
      }
    }
  }
  let cf = 0, cw = 0, cc = 0;
  const d = segImg.data;
  for (let k = 0; k < n; k++) {
    if (dlab[k] === 0) dlab[k] = ceilLike[k] ? 3 : 2;
    const l = dlab[k];
    if (l === 1) { d[4 * k] = 60; d[4 * k + 1] = 255; d[4 * k + 2] = 150; d[4 * k + 3] = 46; cf++; }
    else if (l === 3) { d[4 * k] = 90; d[4 * k + 1] = 160; d[4 * k + 2] = 255; d[4 * k + 3] = 40; cc++; }
    else { d[4 * k] = 255; d[4 * k + 1] = 170; d[4 * k + 2] = 60; d[4 * k + 3] = 22; cw++; }
  }
  det.floorPct = cf / n; det.wallPct = cw / n; det.ceilPct = cc / n;
  segCtx.putImageData(segImg, 0, 0);
  // 可走的地面：把地板像素投到公尺格子
  for (let j = 2; j < DH - 1; j += 3) {
    for (let i = 2; i < DW - 1; i += 3) {
      if (dlab[j * DW + i] !== 1) continue;
      const fp = floorPoint((i + 0.5) * DS, (j + 0.5) * DS);
      if (!fp || fp.d > 7) continue;
      world.free.set(Math.floor(fp.x / 0.5) + ',' + Math.floor(fp.z / 0.5), now);
    }
  }
  if (world.free.size > 5000) {
    const cut = now - 40000;
    for (const [key, t] of world.free) if (t < cut) world.free.delete(key);
  }
}
function segCrossAny(ax, az, bx, bz, cx, cz, dx, dz) {
  const d1x = bx - ax, d1z = bz - az, d2x = dx - cx, d2z = dz - cz;
  const den = d1x * d2z - d1z * d2x;
  if (Math.abs(den) < 1e-9) return false;
  const t = ((cx - ax) * d2z - (cz - az) * d2x) / den;
  const u = ((cx - ax) * d1z - (cz - az) * d1x) / den;
  return t > 0 && t < 1 && u >= 0 && u <= 1;
}
function isFree(x, z) {
  return world.free.has(Math.floor(x / 0.5) + ',' + Math.floor(z / 0.5));
}

// ---------- 5. 世界模型：融合 ----------
function entType(e) {
  const v = e.votes;
  if (v.corner >= 2 && v.corner >= v.column) return 'corner';
  if (v.column >= 2 && v.column >= v.edge) return 'column';
  return v.corner > v.edge ? 'corner' : v.column > v.edge ? 'column' : 'edge';
}

function fuseEnt(o, now) {
  let best = null, bd = 0.7;
  for (const e of world.ents) {
    const d = Math.hypot(e.x - o.x, e.z - o.z);
    if (d < bd) { bd = d; best = e; }
  }
  if (!best) {
    best = { id: world.nid++, x: o.x, z: o.z, w: o.w || 0.3, hits: 0, miss: 0, votes: { corner: 0, column: 0, edge: 0 }, dirs: [], used: 0, pass: 0, born: now };
    world.ents.push(best);
  } else {
    best.x += (o.x - best.x) * 0.25; best.z += (o.z - best.z) * 0.25;
    if (o.type === 'column') best.w += (o.w - best.w) * 0.25;
  }
  best.hits = Math.min(best.hits + 1, 30);
  best.miss = 0; best.pass = world.pass; best.last = now;
  best.votes[o.type]++;
  best.type = entType(best);
  for (const a of o.dirs) {
    let hit = false;
    for (let q = 0; q < best.dirs.length; q++) {
      if (Math.abs(wrapPi(best.dirs[q] - a)) < 15 * DEG) { best.dirs[q] += wrapPi(a - best.dirs[q]) * 0.3; hit = true; break; }
    }
    if (!hit && best.dirs.length < 3) best.dirs.push(a);
  }
}

function fuseWall(w, now) {
  const len = Math.hypot(w.x2 - w.x1, w.z2 - w.z1);
  if (len < 0.8) return;
  const ang = Math.atan2(w.z2 - w.z1, w.x2 - w.x1);
  for (const e of world.walls) {
    const ea = Math.atan2(e.z2 - e.z1, e.x2 - e.x1);
    let da = Math.abs(wrapPi(ang - ea));
    da = Math.min(da, Math.PI - da);
    if (da > 12 * DEG) continue;
    const ux = Math.cos(ea), uz = Math.sin(ea), nx = -uz, nz = ux;
    const off1 = (w.x1 - e.x1) * nx + (w.z1 - e.z1) * nz;
    const off2 = (w.x2 - e.x1) * nx + (w.z2 - e.z1) * nz;
    if (Math.abs(off1) > 0.5 || Math.abs(off2) > 0.5) continue;
    const elen = Math.hypot(e.x2 - e.x1, e.z2 - e.z1);
    const t1 = (w.x1 - e.x1) * ux + (w.z1 - e.z1) * uz, t2 = (w.x2 - e.x1) * ux + (w.z2 - e.z1) * uz;
    const lo = Math.min(0, t1, t2), hi = Math.max(elen, t1, t2);
    if (Math.min(elen, Math.max(t1, t2)) - Math.max(0, Math.min(t1, t2)) < -0.8) continue;
    if (hi - lo > 14) continue;
    const off = ((off1 + off2) / 2) * 0.3;
    e.x1 = e.x1 + ux * lo + nx * off; e.z1 = e.z1 + uz * lo + nz * off;
    e.x2 = e.x1 - ux * lo + ux * hi; e.z2 = e.z1 - uz * lo + uz * hi;
    e.hits = Math.min(e.hits + 1, 30); e.miss = 0; e.pass = world.pass; e.last = now;
    return;
  }
  world.walls.push({ id: world.nid++, x1: w.x1, z1: w.z1, x2: w.x2, z2: w.z2, hits: 1, miss: 0, pass: world.pass, last: now, used: 0 });
}

function inView(x, z, tol) {
  const dx = x - pos.x, dz = z - pos.z, d = Math.hypot(dx, dz);
  if (d < 1.2 || d > 8) return false;
  return Math.abs(wrapPi(Math.atan2(dx, -dz) - Math.atan2(headX, -headZ))) < tol;
}

function decayWorld() {
  const tol = 22 * DEG;
  for (const e of world.ents) {
    if (e.pass === world.pass || !inView(e.x, e.z, tol)) continue;
    if (++e.miss > 10) { e.hits -= 1; e.miss = 0; }
  }
  for (const w of world.walls) {
    if (w.pass === world.pass || !inView((w.x1 + w.x2) / 2, (w.z1 + w.z2) / 2, tol)) continue;
    if (++w.miss > 14) { w.hits -= 1; w.miss = 0; }
  }
  world.ents = world.ents.filter((e) => e.hits > 0);
  world.walls = world.walls.filter((w) => w.hits > 0);
}

// 注入已知的世界資料（測試或匯入外部掃描／點雲時使用）
function injectWorld(ents, walls) {
  const now = performance.now();
  for (const e of ents || []) for (let q = 0; q < 5; q++) fuseEnt({ type: e.type, x: e.x, z: e.z, w: e.w || 0.3, dirs: e.dirs || [] }, now);
  for (const w of walls || []) for (let q = 0; q < 4; q++) fuseWall(w, now);
}

// ---------- 6. 總流程 ----------
function runDetection(now) {
  if (!running || DW < 8) return;
  if (angSpeed > 1.4) { det.skipped++; return; }
  const t0 = performance.now();
  dmctx.drawImage(scene, 0, 0, DW, DH);
  detGradients();
  const thr = Math.max(9, S.dotThreshold * 0.9);
  det.thr = thr;
  runCanny();
  detHarris();
  const lines = detVertical(thr);
  detSegment(thr, now);
  world.pass++;
  const { obsE, obsW } = classifyLines(lines, thr);
  for (const o of obsE) fuseEnt(o, now);
  for (const w of obsW) fuseWall(w, now);
  decayWorld();
  det.passes++;
  det.ms += (performance.now() - t0 - det.ms) * 0.2;
}

async function probeDepth() {
  det.depth = '無（此瀏覽器沒有深度／LiDAR 介面）';
  try {
    if (navigator.xr && navigator.xr.isSessionSupported) {
      const ok = await navigator.xr.isSessionSupported('immersive-ar');
      det.depth = ok
        ? 'WebXR AR 可用，但深度另開 session，這裡仍用單眼估距'
        : '無 WebXR AR（iOS Safari 不支援），改用單眼估距';
    }
  } catch (e) { /* 保持預設 */ }
}

function worldCounts() {
  let col = 0, cor = 0, edg = 0;
  for (const e of world.ents) {
    if (e.hits < 3) continue;
    if (e.type === 'column') col++; else if (e.type === 'corner') cor++; else edg++;
  }
  return { col, cor, edg, wall: world.walls.filter((w) => w.hits >= 2).length };
}

// ---------- 世界模型在 AR 中的呈現（青色，與白色的虛擬建築區分） ----------
function seg3(c, ax, ay, az, bx, by, bz) {
  const near = 0.15;
  let a = toCam(ax - pos.x, ay - EYE, az - pos.z);
  let b = toCam(bx - pos.x, by - EYE, bz - pos.z);
  if (a[2] < near && b[2] < near) return;
  if (a[2] < near) { const t = (near - a[2]) / (b[2] - a[2]); a = [lerp(a[0], b[0], t), lerp(a[1], b[1], t), near]; }
  else if (b[2] < near) { const t = (near - b[2]) / (a[2] - b[2]); b = [lerp(b[0], a[0], t), lerp(b[1], a[1], t), near]; }
  const pa = toScreen(a), pb = toScreen(b);
  c.moveTo(pa[0], pa[1]); c.lineTo(pb[0], pb[1]);
}

function drawWorld(c) {
  c.lineJoin = 'round';
  const H1 = 2.6;
  for (const w of world.walls) {
    if (w.hits < 2) continue;
    const al = Math.min(0.75, 0.25 + w.hits * 0.08);
    c.strokeStyle = `rgba(110,255,225,${al.toFixed(2)})`;
    c.lineWidth = 1.6;
    c.beginPath();
    seg3(c, w.x1, 0, w.z1, w.x2, 0, w.z2);
    seg3(c, w.x1, H1, w.z1, w.x2, H1, w.z2);
    seg3(c, w.x1, 0, w.z1, w.x1, H1, w.z1);
    seg3(c, w.x2, 0, w.z2, w.x2, H1, w.z2);
    const len = Math.hypot(w.x2 - w.x1, w.z2 - w.z1);
    for (let s = 1.5; s < len - 0.5; s += 1.5) {
      const t = s / len, x = lerp(w.x1, w.x2, t), z = lerp(w.z1, w.z2, t);
      seg3(c, x, 0, z, x, H1, z);
    }
    c.stroke();
  }
  for (const e of world.ents) {
    if (e.hits < 3) continue;
    const al = Math.min(0.9, 0.35 + e.hits * 0.06);
    c.strokeStyle = `rgba(110,255,225,${al.toFixed(2)})`;
    c.lineWidth = 2;
    c.beginPath();
    const hh = e.type === 'column' ? 2.8 : 2.6;
    seg3(c, e.x, 0, e.z, e.x, hh, e.z);
    if (e.type === 'column') {
      const r = Math.max(0.12, e.w / 2);
      for (const y of [0, hh]) {
        seg3(c, e.x - r, y, e.z - r, e.x + r, y, e.z - r); seg3(c, e.x + r, y, e.z - r, e.x + r, y, e.z + r);
        seg3(c, e.x + r, y, e.z + r, e.x - r, y, e.z + r); seg3(c, e.x - r, y, e.z + r, e.x - r, y, e.z - r);
      }
    } else if (e.type === 'corner') {
      for (const a of e.dirs) seg3(c, e.x, 0.02, e.z, e.x + Math.cos(a) * 0.6, 0.02, e.z + Math.sin(a) * 0.6);
    }
    c.stroke();
  }
}

// ---------- 偵測層（畫在主畫布上，不受視野限制） ----------
function drawDetOverlay() {
  ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  ctx.imageSmoothingEnabled = true;
  ctx.drawImage(segCv, 0, 0, W, H);
  if (S.showCanny && S.cannyOn) drawCannyOverlay();
  ctx.strokeStyle = 'rgba(255,255,255,0.85)';
  ctx.lineWidth = 1;
  ctx.beginPath();
  for (const f of det.feats) {
    const x = (f.i + 0.5) * DS, y = (f.j + 0.5) * DS;
    ctx.moveTo(x - 3, y); ctx.lineTo(x + 3, y); ctx.moveTo(x, y - 3); ctx.lineTo(x, y + 3);
  }
  ctx.stroke();
  ctx.strokeStyle = 'rgba(110,255,225,0.9)';
  ctx.lineWidth = 1.5;
  ctx.beginPath();
  for (const l of det.vlines) { ctx.moveTo(l.xt, l.yt); ctx.lineTo(l.xb, l.yb); }
  ctx.stroke();
  ctx.font = '11px ui-monospace, Menlo, monospace';
  ctx.textAlign = 'left'; ctx.textBaseline = 'top';
  ctx.fillStyle = 'rgba(110,255,225,0.95)';
  for (const l of det.vlines) {
    if (!l.fp) continue;
    ctx.fillText(l.fp.d.toFixed(1) + 'm', l.xb + 4, Math.min(H - 14, l.yb + 2));
  }
}

// ==========================================================
// Canny 邊緣偵測（在偵測格 DS×DS 上，每次偵測執行一次）
//   1 高斯模糊 5×5（σ≈1.0）          抑制雜訊，避免地磚紋與影像顆粒變成邊緣
//   2 Sobel 梯度（強度、方向）
//   3 非極大值抑制                    沿梯度方向只保留最強的一個像素 → 邊緣細成 1 像素
//   4 雙閾值                          強邊緣（≥ high）、弱邊緣（≥ low）
//   5 遲滯                            弱邊緣只有「連得到強邊緣」才保留，斷斷續續的線被接起來
// 結果 cmask：0 無、1 弱（已連到強邊緣）、2 強。
// 用途：垂直線偵測、轉角的地牆交線追蹤、外圍點雲（只在真正的物體邊緣留白點）、疊圖顯示。
// 閾值跟著「點雲敏感度」滑桿：high = 敏感度 × 0.9，low = high × 0.4。
// ==========================================================
let cg = new Float32Array(1), cgm = new Float32Array(1), cmask = new Uint8Array(1), cdir = new Uint8Array(1), cnms = new Float32Array(1);
let cstack = new Int32Array(1);
const cn = { n: 0, strong: 0, ms: 0, high: 0, low: 0, at: 0, img: null, cv: null, cx: null };
const GK = [1 / 16, 4 / 16, 6 / 16, 4 / 16, 1 / 16]; // 二項式近似高斯（σ≈1.0）

function cannyResize() {
  const n = DW * DH;
  cg = new Float32Array(n); cgm = new Float32Array(n); cmask = new Uint8Array(n);
  cdir = new Uint8Array(n); cnms = new Float32Array(n); cstack = new Int32Array(n);
  cn.cv = document.createElement('canvas');
  cn.cv.width = DW; cn.cv.height = DH;
  cn.cx = cn.cv.getContext('2d');
  cn.img = cn.cx.createImageData(DW, DH);
  cn.at = 0;
}

function runCanny() {
  const t0 = performance.now();
  const n = DW * DH;
  // 1 高斯（可分離）：先水平、再垂直，暫存在 cnms
  for (let j = 0; j < DH; j++) {
    for (let i = 0; i < DW; i++) {
      let s = 0;
      for (let q = -2; q <= 2; q++) {
        const ii = i + q < 0 ? 0 : i + q >= DW ? DW - 1 : i + q;
        s += dgray[j * DW + ii] * GK[q + 2];
      }
      cnms[j * DW + i] = s;
    }
  }
  for (let j = 0; j < DH; j++) {
    for (let i = 0; i < DW; i++) {
      let s = 0;
      for (let q = -2; q <= 2; q++) {
        const jj = j + q < 0 ? 0 : j + q >= DH ? DH - 1 : j + q;
        s += cnms[jj * DW + i] * GK[q + 2];
      }
      cg[j * DW + i] = s;
    }
  }
  // 2 Sobel 強度與量化方向（0＝水平梯度、1＝45°、2＝垂直梯度、3＝135°）
  cgm.fill(0);
  for (let j = 1; j < DH - 1; j++) {
    for (let i = 1; i < DW - 1; i++) {
      const k = j * DW + i;
      const gx = (-cg[k - DW - 1] + cg[k - DW + 1] - 2 * cg[k - 1] + 2 * cg[k + 1] - cg[k + DW - 1] + cg[k + DW + 1]) / 4;
      const gy = (-cg[k - DW - 1] - 2 * cg[k - DW] - cg[k - DW + 1] + cg[k + DW - 1] + 2 * cg[k + DW] + cg[k + DW + 1]) / 4;
      const m = Math.sqrt(gx * gx + gy * gy);
      cgm[k] = m;
      if (m < 1e-3) { cdir[k] = 0; continue; }
      const ax = Math.abs(gx), ay = Math.abs(gy);
      if (ay <= ax * 0.4142) cdir[k] = 0;
      else if (ay >= ax * 2.4142) cdir[k] = 2;
      else cdir[k] = (gx * gy > 0) ? 1 : 3;
    }
  }
  // 3 非極大值抑制 + 4 雙閾值
  const high = Math.max(8, S.dotThreshold * 0.9);
  const low = high * 0.4;
  cn.high = high; cn.low = low;
  cmask.fill(0);
  let sp = 0;
  for (let j = 2; j < DH - 2; j++) {
    for (let i = 2; i < DW - 2; i++) {
      const k = j * DW + i, m = cgm[k];
      if (m < low) continue;
      let a, b;
      switch (cdir[k]) {
        case 0: a = cgm[k - 1]; b = cgm[k + 1]; break;
        case 2: a = cgm[k - DW]; b = cgm[k + DW]; break;
        case 1: a = cgm[k - DW - 1]; b = cgm[k + DW + 1]; break;
        default: a = cgm[k - DW + 1]; b = cgm[k + DW - 1];
      }
      if (m <= a || m < b) continue; // 平台（相等）時只留一側，邊緣才會是 1 像素寬
      if (m >= high) { cmask[k] = 2; cstack[sp++] = k; }
      else cmask[k] = 1; // 候選弱邊緣，待遲滯確認
    }
  }
  // 5 遲滯：從強邊緣出發，連到的弱邊緣升格；沒連到的清掉
  const keep = new Uint8Array(n);
  for (let q = 0; q < sp; q++) keep[cstack[q]] = 1;
  let top = sp;
  while (top > 0) {
    const k = cstack[--top];
    for (let b = -1; b <= 1; b++) {
      for (let a = -1; a <= 1; a++) {
        const nk = k + b * DW + a;
        if (cmask[nk] === 1 && !keep[nk]) { keep[nk] = 1; cstack[top++] = nk; }
      }
    }
  }
  let cnt = 0, strong = 0;
  for (let k = 0; k < n; k++) {
    if (cmask[k] === 1 && !keep[k]) cmask[k] = 0;
    if (cmask[k]) { cnt++; if (cmask[k] === 2) strong++; }
  }
  cn.n = cnt; cn.strong = strong;
  cn.at = performance.now();
  cn.ms += (performance.now() - t0 - cn.ms) * 0.2;
}

function cannyFresh() { return S.cannyOn && cn.at > 0 && performance.now() - cn.at < 600; }

// 疊圖：強邊緣＝黃、弱邊緣（連到強邊緣者）＝洋紅
function drawCannyOverlay() {
  if (!cn.cx || !cn.img) return;
  const d = cn.img.data, n = DW * DH;
  for (let k = 0; k < n; k++) {
    const m = cmask[k];
    if (m === 2) { d[4 * k] = 255; d[4 * k + 1] = 220; d[4 * k + 2] = 60; d[4 * k + 3] = 235; }
    else if (m === 1) { d[4 * k] = 255; d[4 * k + 1] = 90; d[4 * k + 2] = 200; d[4 * k + 3] = 200; }
    else d[4 * k + 3] = 0;
  }
  cn.cx.putImageData(cn.img, 0, 0);
  ctx.save();
  ctx.imageSmoothingEnabled = false;
  ctx.drawImage(cn.cv, 0, 0, DW * DS, DH * DS);
  ctx.restore();
}

// ==========================================================
// 連線（自架 WebSocket）：多位玩家同一基地、同一房間
//   送出：約每 100 ms 一筆位姿。已對位（al.ok）送 site 座標（所有人共用的基地座標），
//         未對位送 AR 座標（各人自己的座標，彼此不能比較，只顯示在清單）。
//   接收：房間快照（每 100 ms）→ 其他玩家平滑內插 → 畫在 AR 畫面（同樣受視野規則限制、
//         被模型牆擋住就不畫）與羅盤雷達；共享狀態 state；一次性事件 event。
//   訊息格式見 server/server.js 開頭與 README。
// ==========================================================
const net = {
  ws: null, on: false, want: false, url: '', room: '', name: '', token: '', id: 0, color: '#fff',
  others: new Map(), state: {}, rtt: 0, nPlayers: 0, retry: 0, retryAt: 0, lastSend: 0, lastPing: 0,
  msg: '未連線', sitePublished: false, events: [],
};

function netNormUrl(u) {
  u = (u || '').trim();
  if (!u) return '';
  u = u.replace(/^http:\/\//i, 'ws://').replace(/^https:\/\//i, 'wss://');
  if (!/^wss?:\/\//i.test(u)) u = (/^(localhost|127\.|192\.168\.|10\.)/.test(u) ? 'ws://' : 'wss://') + u;
  return u;
}

function netStatusEls() {
  const s = document.getElementById('nStatus');
  if (s) s.textContent = net.msg;
  const b = document.getElementById('bNet');
  if (b) { b.textContent = net.on ? '中斷連線' : (net.want ? '連線中…（取消）' : '連線'); b.classList.toggle('on', net.on); }
}

function netConnect() {
  const url = netNormUrl((document.getElementById('nUrl') || {}).value || net.url);
  const room = ((document.getElementById('nRoom') || {}).value || net.room || 'room1').trim();
  const name = ((document.getElementById('nName') || {}).value || net.name || '').trim();
  const tok = ((document.getElementById('nToken') || {}).value || net.token || '');
  if (!url) { net.msg = '請先填伺服器網址'; netStatusEls(); return; }
  if (location.protocol === 'https:' && /^ws:\/\//i.test(url) && !/^ws:\/\/(localhost|127\.)/.test(url)) {
    net.msg = '網頁是 https，只能連 wss:// 的伺服器（見 README：用 https 隧道或雲端主機）';
    netStatusEls(); return;
  }
  if (!/^[A-Za-z0-9_-]{1,16}$/.test(room)) { net.msg = '房間代碼只能用英數字與 - _，最長 16 字'; netStatusEls(); return; }
  net.url = url; net.room = room; net.name = name; net.token = tok; net.want = true; net.retry = 0;
  try { localStorage.setItem('arVision.net', JSON.stringify({ url, room, name })); } catch (e) { /* ignore */ }
  netOpen();
}

function netOpen() {
  if (net.ws) { try { net.ws.onclose = null; net.ws.close(); } catch (e) { /* ignore */ } }
  net.msg = '連線中…'; netStatusEls();
  let ws;
  try { ws = new WebSocket(net.url); } catch (e) { net.msg = '網址格式不對'; net.want = false; netStatusEls(); return; }
  net.ws = ws;
  ws.onopen = () => {
    ws.send(JSON.stringify({ t: 'join', room: net.room, name: net.name || undefined, role: 'player', token: net.token || undefined }));
  };
  ws.onmessage = (e) => { let m; try { m = JSON.parse(e.data); } catch (x) { return; } netHandle(m); };
  ws.onclose = () => {
    const was = net.on;
    net.on = false; net.others.clear(); net.nPlayers = 0;
    if (net.want) {
      net.retry = Math.min(net.retry + 1, 6);
      net.retryAt = performance.now() + Math.min(15000, 800 * Math.pow(2, net.retry));
      net.msg = (was ? '連線中斷，' : '連不上，') + '重試中…';
    } else if (!net.errShown) net.msg = '未連線';
    net.errShown = false;
    netStatusEls();
  };
  ws.onerror = () => {};
}

function netDisconnect() {
  net.want = false;
  if (net.ws) { try { net.ws.close(); } catch (e) { /* ignore */ } }
  net.on = false; net.others.clear(); net.nPlayers = 0; net.msg = '未連線'; netStatusEls();
}

function netSend(o) { if (net.ws && net.ws.readyState === 1) net.ws.send(JSON.stringify(o)); }

function netHandle(m) {
  if (m.t === 'welcome') {
    net.on = true; net.id = m.id || 0; net.color = m.color || '#fff'; net.state = m.state || {};
    net.msg = `已連線：房間 ${m.room}`; net.retry = 0; net.sitePublished = false;
    if (m.snap) netSnap(m.snap);
    mkNetInit(m.markers);
    netStatusEls();
    return;
  }
  if (m.t === 'snap') { netSnap(m); return; }
  if (m.t === 'mk') { mkNetAdd(Object.assign({ lid: m.m.lid }, m.m)); return; }
  if (m.t === 'mkmap') { mkNetMap(m); return; }
  if (m.t === 'mkact') { mkNetAct(m); return; }
  if (m.t === 'state') {
    if (m.val === null) delete net.state[m.key]; else net.state[m.key] = m.val;
    net.events.push({ kind: 'state', key: m.key, val: m.val, by: m.by });
    return;
  }
  if (m.t === 'event') {
    net.events.push(m);
    const who = (net.others.get(m.by) || {}).name || ('玩家' + m.by);
    if (m.kind === 'suspense') say(`${who} 遇到了：${m.data && m.data.name ? m.data.name : '異狀'}`, 3000);
    else if (m.kind === 'aligned') say(`${who} 完成對位`, 2200);
    else if (m.kind === 'say') say(`${who}：${String(m.data).slice(0, 40)}`, 3200);
    return;
  }
  if (m.t === 'join') { say(`${m.name} 加入了房間`, 2200); return; }
  if (m.t === 'leave') { net.others.delete(m.id); return; }
  if (m.t === 'reset') { net.state = {}; mkReset(); say('遊戲已重置', 2200); return; }
  if (m.t === 'pong') { if (m.ts) net.rtt += (performance.now() - m.ts - net.rtt) * 0.3; return; }
  if (m.t === 'error') { net.msg = m.msg || '伺服器拒絕連線'; net.want = false; net.errShown = true; netStatusEls(); }
}

function netSnap(s) {
  const seen = new Set();
  for (const p of s.players || []) {
    if (p.id === net.id) continue;
    seen.add(p.id);
    let o = net.others.get(p.id);
    if (!o) { o = { id: p.id, sx: p.x, sz: p.z, sh: p.h }; net.others.set(p.id, o); }
    o.name = p.name; o.color = p.color; o.x = p.x; o.z = p.z; o.h = p.h; o.frame = p.frame; o.steps = p.steps; o.seen = performance.now();
    if (o.frame !== o.lastFrame) { o.sx = p.x; o.sz = p.z; o.lastFrame = o.frame; }
  }
  for (const id of [...net.others.keys()]) if (!seen.has(id)) net.others.delete(id);
  net.nPlayers = (s.players || []).length;
}

// 共享狀態與事件（給遊戲邏輯用，例如謎題旗標）
function netSetState(key, val) { netSend({ t: 'state', key, val }); }
function netEvent(kind, data) { netSend({ t: 'event', kind, data }); }

// ---------- 每格 ----------
function netTick(dt, now) {
  if (net.want && !net.on && (!net.ws || net.ws.readyState > 1) && now >= net.retryAt) netOpen();
  if (!net.on) return;
  // 平滑其他玩家
  const k = Math.min(1, dt * 8);
  for (const o of net.others.values()) {
    o.sx += (o.x - o.sx) * k; o.sz += (o.z - o.sz) * k;
    o.sh = o.sh + wrapPi((o.h - o.sh) * DEG) / DEG * k;
  }
  if (running && now - net.lastSend >= 100) {
    net.lastSend = now;
    if (al.ok) netSend({ t: 'pose', frame: 'site', x: alR.x, z: alR.z, h: alR.h, steps });
    else netSend({ t: 'pose', frame: 'ar', x: pos.x, z: pos.z, h: ((Math.atan2(headX, -headZ) / DEG) + 360) % 360, steps });
  }
  if (now - net.lastPing > 5000) { net.lastPing = now; netSend({ t: 'ping', ts: performance.now() }); }
  // 對位完成後，把基地模型發佈到房間（指揮端用它畫地圖），並通知大家
  if (al.ok && !net.sitePublished) {
    net.sitePublished = true;
    if (!net.state.site) netSetState('site', { walls: siteWalls(), items: siteItems().map((i) => ({ k: i.k, x: +i.x.toFixed(2), z: +i.z.toFixed(2) })) });
    netEvent('aligned', null);
  }
  if (!al.ok) net.sitePublished = false;
}

// 同一個基地座標系裡的其他玩家（我已對位、對方也已對位）
function netPeers() {
  const out = [];
  if (!net.on || !al.ok) return out;
  for (const o of net.others.values()) {
    if (o.frame !== 'site') continue;
    const a = siteToAR(o.sx, o.sz);
    if (!a) continue;
    let hidden = false;
    for (const w of siteWalls()) {
      if (segCrossAny(alR.x, alR.z, o.sx, o.sz, w[0], w[1], w[2], w[3])) { hidden = true; break; }
    }
    out.push({ o, x: a[0], z: a[1], hidden, d: Math.hypot(o.sx - alR.x, o.sz - alR.z) });
  }
  return out;
}

// 其他玩家改由 people.js 以白色框標示（敵人），這裡不再畫線條人形與名牌
function drawNet() {}
function drawNetOverlay() {}

// 羅盤雷達：其他玩家（含未對位者不顯示——座標不可比較）
function netRadar(put) {
  for (const p of netPeers()) put(p.x, p.z, p.o.color, 3);
}

function netHudLine() {
  if (!net.want && !net.on) return null;
  if (!net.on) return `> 連線：${net.msg}`;
  const unaligned = [...net.others.values()].filter((o) => o.frame !== 'site').length;
  return `> 連線：${net.room}　${net.nPlayers} 人　${net.rtt.toFixed(0)}ms${al.ok ? '' : '　（自己未對位，看不到他人位置）'}${unaligned && al.ok ? `　${unaligned} 人未對位` : ''}`;
}

function netInit() {
  try {
    const raw = localStorage.getItem('arVision.net');
    if (raw) { const v = JSON.parse(raw); net.url = v.url || ''; net.room = v.room || ''; net.name = v.name || ''; }
  } catch (e) { /* ignore */ }
  let auto = false;
  // 從伺服器的 /play/ 開啟時，伺服器網址就是這個網頁的來源
  if (/\/play\/?$/.test(location.pathname)) net.url = (location.protocol === 'https:' ? 'wss://' : 'ws://') + location.host;
  try {
    const q = new URLSearchParams(location.search);
    if (q.get('server')) { net.url = q.get('server'); auto = true; }
    if (q.get('room')) net.room = q.get('room');
    if (q.get('name')) net.name = q.get('name');
  } catch (e) { /* ignore */ }
  const set = (id, v) => { const el = document.getElementById(id); if (el && v) el.value = v; };
  set('nUrl', net.url); set('nRoom', net.room || 'room1'); set('nName', net.name);
  const b = document.getElementById('bNet');
  if (b) b.addEventListener('click', () => { if (net.on || net.want) netDisconnect(); else netConnect(); });
  net.autoConnect = auto;
  netStatusEls();
}

// ==========================================================
// 方位：陀螺儀 + 羅盤（右上角）
//   短時間：方向感測器（陀螺儀融合）給出平滑的視線方向
//   長時間：磁北量測（iOS webkitCompassHeading／Android deviceorientationabsolute）
//   用互補濾波估計「遊戲前方」相對磁北的偏移 nOff，兩者相加就是磁北方位
// ==========================================================
const cmp = { nOff: 0, have: false, absSeen: false, src: '相對（無羅盤）', deg: 0, pitch: 0, roll: 0, gyro: 0, lastMeas: 0 };
let SAFE_TOP = 0;

function safeTop() {
  try {
    const d = document.createElement('div');
    d.style.cssText = 'position:fixed;top:0;left:0;padding-top:env(safe-area-inset-top,0px);visibility:hidden;pointer-events:none';
    document.body.appendChild(d);
    const v = parseFloat(getComputedStyle(d).paddingTop) || 0;
    d.remove();
    return v;
  } catch (e) { return 0; }
}

function gameHeading() { return Math.atan2(headX, -headZ); }

function cmpMeas(bearing, src) {
  const gh = gameHeading();
  const off = wrapPi(bearing - gh);
  if (!cmp.have) { cmp.nOff = off; cmp.have = true; }
  else cmp.nOff = wrapPi(cmp.nOff + wrapPi(off - cmp.nOff) * 0.04);
  cmp.src = src;
  cmp.lastMeas = performance.now();
}

// iOS：deviceorientation 事件附帶 webkitCompassHeading（相機朝向的磁北方位，度）
function cmpFromEvent(e) {
  if (e.webkitCompassHeading != null && !isNaN(e.webkitCompassHeading) && B.F && Math.hypot(B.F[0], B.F[2]) > 0.5) {
    cmpMeas(e.webkitCompassHeading * DEG, '磁北（iOS 羅盤＋陀螺儀）');
  }
}

// Android：deviceorientationabsolute 的 alpha 以磁北為基準
function onOrientAbs(e) {
  if (e.alpha == null || e.beta == null || e.gamma == null) return;
  cmp.absSeen = true;
  const x = e.beta * DEG, y = e.gamma * DEG, z = e.alpha * DEG;
  const cX = Math.cos(x), cY = Math.cos(y), cZ = Math.cos(z), sX = Math.sin(x), sY = Math.sin(y), sZ = Math.sin(z);
  const e0 = -(cY * sZ * sX + cZ * sY); // 後鏡頭朝向：東
  const n0 = -(sZ * sY - cZ * cY * sX); // 北
  if (Math.hypot(e0, n0) < 0.5) return;
  cmpMeas(Math.atan2(e0, n0), '磁北（Android 羅盤＋陀螺儀）');
}

function updateCompass() {
  cmp.deg = ((gameHeading() + cmp.nOff) / DEG + 360 * 4) % 360;
  cmp.pitch = Math.asin(Math.max(-1, Math.min(1, B.F[1]))) / DEG;
  cmp.roll = Math.atan2(B.sr[1], B.su[1]) / DEG;
}

const CARD = ['北', '東北', '東', '東南', '南', '西南', '西', '西北'];
function cardinal(deg) { return CARD[Math.round(deg / 45) % 8]; }

function drawCompass() {
  const R = 36, cx = W - R - 12, cy = SAFE_TOP + R + 10;
  ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  ctx.save();
  ctx.fillStyle = 'rgba(0,0,0,0.6)';
  ctx.strokeStyle = 'rgba(255,255,255,0.55)';
  ctx.lineWidth = 1;
  ctx.beginPath(); ctx.arc(cx, cy, R, 0, Math.PI * 2); ctx.fill(); ctx.stroke();
  const rel = (bearingDeg) => (bearingDeg - cmp.deg) * DEG; // 螢幕上方 = 目前朝向
  // 刻度與方位字
  for (let a = 0; a < 360; a += 30) {
    const t = rel(a), s = Math.sin(t), c = -Math.cos(t);
    const major = a % 90 === 0;
    ctx.strokeStyle = 'rgba(255,255,255,' + (major ? 0.9 : 0.4) + ')';
    ctx.beginPath();
    ctx.moveTo(cx + s * (R - (major ? 9 : 5)), cy + c * (R - (major ? 9 : 5)));
    ctx.lineTo(cx + s * (R - 1), cy + c * (R - 1));
    ctx.stroke();
  }
  ctx.font = '600 11px -apple-system, "PingFang TC", sans-serif';
  ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
  [['N', 0, '#ff6a5a'], ['E', 90, '#fff'], ['S', 180, '#fff'], ['W', 270, '#fff']].forEach(([L, a, col]) => {
    const t = rel(a);
    ctx.fillStyle = col;
    ctx.fillText(L, cx + Math.sin(t) * (R - 18), cy - Math.cos(t) * (R - 18));
  });
  // 世界模型實體與虛擬建築的方位（雷達點）
  const put = (x, z, col, r) => {
    const b = Math.atan2(x - pos.x, -(z - pos.z)); // 遊戲座標方位（弧度）
    const tt = b + cmp.nOff - cmp.deg * DEG; // 相對於目前朝向
    ctx.fillStyle = col;
    ctx.beginPath(); ctx.arc(cx + Math.sin(tt) * (R - 4), cy - Math.cos(tt) * (R - 4), r, 0, Math.PI * 2); ctx.fill();
  };
  for (const e of world.ents) if (e.hits >= 3) put(e.x, e.z, 'rgba(110,255,225,0.95)', 2);
  for (const o of obs) if (o.gen && !o.dying) put(o.x, o.z, 'rgba(255,255,255,0.9)', 1.6);
  netRadar(put);
  mkRadar(put);
  ppRadar(put);
  // 內圈：人工地平線（俯仰與滾轉）
  ctx.save();
  ctx.beginPath(); ctx.arc(cx, cy, 11, 0, Math.PI * 2); ctx.clip();
  ctx.translate(cx, cy);
  ctx.rotate((-cmp.roll * DEG));
  const off = Math.max(-10, Math.min(10, cmp.pitch * 0.2));
  ctx.fillStyle = 'rgba(90,160,255,0.55)'; ctx.fillRect(-14, -14 + off, 28, 14);
  ctx.fillStyle = 'rgba(160,110,60,0.65)'; ctx.fillRect(-14, off, 28, 14);
  ctx.strokeStyle = '#fff'; ctx.beginPath(); ctx.moveTo(-14, off); ctx.lineTo(14, off); ctx.stroke();
  ctx.restore();
  // 固定的朝向標記
  ctx.fillStyle = '#fff';
  ctx.beginPath(); ctx.moveTo(cx, cy - R - 1); ctx.lineTo(cx - 5, cy - R - 9); ctx.lineTo(cx + 5, cy - R - 9); ctx.closePath(); ctx.fill();
  // 數值
  ctx.font = '600 12px ui-monospace, Menlo, monospace';
  ctx.textAlign = 'right'; ctx.textBaseline = 'top';
  const ty = cy + R + 6;
  const lines = [
    `${String(Math.round(cmp.deg) % 360).padStart(3, '0')}° ${cardinal(cmp.deg)}`,
    `俯仰 ${cmp.pitch >= 0 ? '+' : ''}${cmp.pitch.toFixed(0)}° 滾轉 ${cmp.roll >= 0 ? '+' : ''}${cmp.roll.toFixed(0)}°`,
    `陀螺 ${cmp.gyro.toFixed(0)}°/s`,
  ];
  ctx.fillStyle = 'rgba(0,0,0,0.5)';
  const bw = 132;
  ctx.fillRect(W - bw - 8, ty - 3, bw, 15 * lines.length + 6);
  ctx.fillStyle = 'rgba(255,255,255,0.92)';
  lines.forEach((t, i) => ctx.fillText(t, W - 12, ty + i * 15));
  ctx.font = '10px -apple-system, "PingFang TC", sans-serif';
  ctx.fillStyle = cmp.have ? 'rgba(160,255,230,0.9)' : 'rgba(255,200,120,0.95)';
  ctx.fillText(cmp.src, W - 12, ty + lines.length * 15 + 5);
  ctx.restore();
}

// ==========================================================
// AR 懸疑場景
//   觸發：使用者「隨機移動」（轉向忽左忽右、速度忽快忽慢）→ erratic 分數升高，
//   或長時間沒有事件時小機率觸發。事件都貼著研究主題：看得到的範圍 vs 研判。
//   1 周邊人影：只在視野邊緣出現，一看向中央就消失，再出現時更近
//   2 牆上多一扇門：長在世界模型偵測到的牆上，模型裡原本沒有
//   3 視野閃爍：中央區忽然收縮、閃爍
//   4 腳步聲：立體聲腳步由遠而近＋震動
//   5 訊號故障：畫面切片錯位、字幕亂碼
//   6 邊緣低語：只出現在黑色周邊區的文字
//   不含任何攻擊或傷害判定（威脅物仍關閉）。
// ==========================================================
const susp = {
  fovMul: 1, erratic: 0, yawAbs: 0, rev: 0, lastSign: 0, spdJit: 0, prevSpeed: 0, prevYaw: 0,
  next: 0, lastEv: 0, count: 0, last: '', ac: null,
  fig: null, door: null, flicker: null, glitchUntil: 0, flashUntil: 0, flashA: 0,
  sub: null, edge: null,
};

function audioInit() {
  try {
    const AC = window.AudioContext || window.webkitAudioContext;
    if (AC && !susp.ac) susp.ac = new AC();
    if (susp.ac && susp.ac.state === 'suspended') susp.ac.resume();
  } catch (e) { susp.ac = null; }
}
function noiseBuf(ac, sec) {
  const b = ac.createBuffer(1, Math.floor(ac.sampleRate * sec), ac.sampleRate), d = b.getChannelData(0);
  for (let i = 0; i < d.length; i++) d[i] = Math.random() * 2 - 1;
  return b;
}
function sfxSteps(pan, n) {
  const ac = susp.ac;
  if (!ac) return;
  let t = ac.currentTime + 0.05;
  for (let i = 0; i < n; i++) {
    const src = ac.createBufferSource(); src.buffer = noiseBuf(ac, 0.12);
    const f = ac.createBiquadFilter(); f.type = 'lowpass'; f.frequency.value = 380 + i * 40;
    const g = ac.createGain(); const vol = 0.12 + i * 0.07;
    g.gain.setValueAtTime(0, t); g.gain.linearRampToValueAtTime(vol, t + 0.01); g.gain.exponentialRampToValueAtTime(0.001, t + 0.12);
    let node = g;
    if (ac.createStereoPanner) { const p = ac.createStereoPanner(); p.pan.value = pan * (1 - i * 0.08); g.connect(p); node = p; }
    src.connect(f); f.connect(g); node.connect(ac.destination);
    src.start(t);
    t += 0.62 - i * 0.04;
  }
}
function sfxThump() {
  const ac = susp.ac;
  if (!ac) return;
  const o = ac.createOscillator(), g = ac.createGain(), t = ac.currentTime;
  o.type = 'sine'; o.frequency.setValueAtTime(70, t); o.frequency.exponentialRampToValueAtTime(38, t + 0.5);
  g.gain.setValueAtTime(0.4, t); g.gain.exponentialRampToValueAtTime(0.001, t + 0.6);
  o.connect(g); g.connect(ac.destination); o.start(t); o.stop(t + 0.65);
}
function sfxCreak() {
  const ac = susp.ac;
  if (!ac) return;
  const o = ac.createOscillator(), g = ac.createGain(), f = ac.createBiquadFilter(), t = ac.currentTime;
  o.type = 'sawtooth'; o.frequency.setValueAtTime(110, t); o.frequency.linearRampToValueAtTime(170, t + 1.1);
  f.type = 'bandpass'; f.frequency.value = 600; f.Q.value = 6;
  g.gain.setValueAtTime(0, t); g.gain.linearRampToValueAtTime(0.07, t + 0.2); g.gain.linearRampToValueAtTime(0, t + 1.2);
  o.connect(f); f.connect(g); g.connect(ac.destination); o.start(t); o.stop(t + 1.25);
}
function buzz(p) { try { if (navigator.vibrate) navigator.vibrate(p); } catch (e) { /* ignore */ } }

function say(text, ms) { susp.sub = { text, born: performance.now(), until: performance.now() + (ms || 4200) }; }
function whisperEdge(text, ms) {
  susp.edge = { text, born: performance.now(), until: performance.now() + (ms || 4800), side: Math.random() < 0.5 ? -1 : 1, y: rand(0.3, 0.7) };
}

// ---------- 事件 ----------
function bearingTo(x, z) { return wrapPi(Math.atan2(x - pos.x, -(z - pos.z)) - gameHeading()); }

function halfH() { return Math.max(12 * DEG, Math.atan((W / 2) / FPX)); } // 螢幕水平半視角

function spotOk(x, z) {
  for (const w of world.walls) if (w.hits >= 2 && segCrossAny(pos.x, pos.z, x, z, w.x1, w.z1, w.x2, w.z2)) return false; // 隔著牆
  for (const o of obs) if (!o.dying && distPointBox(x, z, o) < 0.5) return false;
  return true;
}

function placeFigure(now, dist, hops) {
  // 優先躲在視野邊緣方向的柱子／轉角後；否則放在邊緣方位的可站立地面上
  const best = world.ents
    .filter((e) => e.hits >= 3 && e.type !== 'edge')
    .map((e) => ({ e, b: bearingTo(e.x, e.z), d: Math.hypot(e.x - pos.x, e.z - pos.z) }))
    .filter((q) => Math.abs(q.b) > 0.5 * halfH() && Math.abs(q.b) < 1.0 * halfH() && q.d > 3 && q.d < 10)
    .sort((p, q) => Math.abs(Math.abs(p.b) - 0.75 * halfH()) - Math.abs(Math.abs(q.b) - 0.75 * halfH()))[0];
  if (best && hops === 0) {
    const dx = best.e.x - pos.x, dz = best.e.z - pos.z, d = Math.hypot(dx, dz) || 1;
    const sd = best.b > 0 ? 1 : -1;
    const x = best.e.x + (-dz / d) * 0.5 * sd + (dx / d) * 0.4, z = best.e.z + (dx / d) * 0.5 * sd + (dz / d) * 0.4;
    if (spotOk(x, z)) return { x, z, hide: true };
  }
  for (let k = 0; k < 40; k++) {
    const side = Math.random() < 0.5 ? -1 : 1;
    const a = gameHeading() + side * rand(0.6, 0.95) * halfH();
    const d = Math.max(2.6, dist * rand(0.45, 1.05));
    const x = pos.x + Math.sin(a) * d, z = pos.z - Math.cos(a) * d;
    if (spotOk(x, z)) return { x, z, hide: false };
  }
  return null;
}

function evFigure(now) {
  const spot = placeFigure(now, rand(5, 7.5), 0);
  if (!spot) return false;
  susp.fig = { x: spot.x, z: spot.z, born: now, vanish: 0, hops: 0, fail: 0, seenCenter: 0, respawnAt: 0, seed: Math.random() * 100 };
  whisperEdge('視野邊緣，好像有人', 4200);
  buzz([20]);
  return true;
}
function updateFigure(dt, now) {
  const f = susp.fig;
  if (!f) return;
  if (f.vanish) {
    if (now - f.vanish > 800 && !f.respawnAt) {
      if (f.hops >= 3) { susp.fig = null; say('你一直在看錯的地方', 3600); return; }
      f.respawnAt = now + rand(1400, 2600);
    }
    if (f.respawnAt && now >= f.respawnAt) {
      const d0 = Math.hypot(f.x - pos.x, f.z - pos.z);
      const sp = placeFigure(now, Math.max(2.8, d0 - 1.3), f.hops + 1);
      if (!sp) { f.respawnAt = now + 1000; if (++f.fail > 5) susp.fig = null; return; }
      f.x = sp.x; f.z = sp.z; f.vanish = 0; f.respawnAt = 0; f.hops++; f.born = now; f.seenCenter = 0;
      if (f.hops === 1) whisperEdge('它又出現了，離你更近', 3600);
      sfxSteps(bearingTo(f.x, f.z) > 0 ? 0.7 : -0.7, 2);
    }
    return;
  }
  const b = Math.abs(bearingTo(f.x, f.z)), d = Math.hypot(f.x - pos.x, f.z - pos.z);
  const inside = b < Math.max(6 * DEG, 0.42 * halfH()) && d < 12;
  f.seenCenter = inside ? f.seenCenter + dt : Math.max(0, f.seenCenter - dt * 2);
  if (f.seenCenter > 0.35 || d < 2.2) {
    f.vanish = now;
    susp.glitchUntil = now + 260; susp.flashUntil = now + 120; susp.flashA = 0.5;
    sfxThump();
  }
}

function evDoor(now) {
  const cand = world.walls
    .filter((w) => w.hits >= 2 && Math.hypot(w.x2 - w.x1, w.z2 - w.z1) >= 1.6)
    .map((w) => {
      const mx = (w.x1 + w.x2) / 2, mz = (w.z1 + w.z2) / 2;
      return { w, d: Math.hypot(mx - pos.x, mz - pos.z), b: Math.abs(bearingTo(mx, mz)) };
    })
    .filter((q) => q.d > 2 && q.d < 8 && q.b < 70 * DEG)
    .sort((p, q) => p.b - q.b)[0];
  if (!cand) return false;
  const s = sideOf(cand.w);
  const t = rand(0.35, 0.65);
  const x = cand.w.x1 + (cand.w.x2 - cand.w.x1) * t + s.nx * 0.04;
  const z = cand.w.z1 + (cand.w.z2 - cand.w.z1) * t + s.nz * 0.04;
  susp.door = { x, z, rot: Math.atan2(s.uz, s.ux), nx: s.nx, nz: s.nz, born: now, closeAt: 0 };
  say('牆上多了一扇門——模型裡原本沒有', 4600);
  sfxCreak(); buzz([40, 50, 40]);
  susp.flicker = { start: now, dur: 900 };
  return true;
}
function updateDoor(now) {
  const d = susp.door;
  if (!d) return;
  const dist = Math.hypot(d.x - pos.x, d.z - pos.z);
  if (!d.closeAt && (dist < 1.7 || now - d.born > 16000)) {
    d.closeAt = now;
    if (dist < 1.7) { sfxThump(); susp.flashUntil = now + 140; susp.flashA = 0.6; say('門關上了，牆又平了', 3200); }
  }
  if (d.closeAt && now - d.closeAt > 700) susp.door = null;
}

function evBlackout(now) {
  susp.flicker = { start: now, dur: 1700 };
  say('視野收縮', 2600);
  sfxThump(); buzz([60, 40, 60, 40, 90]);
}
function evSteps() {
  const side = Math.random() < 0.5 ? -1 : 1;
  sfxSteps(side * 0.85, 5);
  buzz([15, 150, 15, 150, 25, 140, 35]);
  say(side < 0 ? '左後方有腳步聲' : '右後方有腳步聲', 3600);
}
function evGlitch(now) {
  susp.glitchUntil = now + 700;
  say('訊號中斷　重新定位中…', 2600);
  sfxThump();
  // 世界模型暫時「失真」：把實體位置抖動一點，之後由偵測慢慢修正
  for (const e of world.ents) { e.x += rand(-0.15, 0.15); e.z += rand(-0.15, 0.15); }
}
const WHISPERS = ['你剛剛走過這裡嗎？', '牆的位置和剛才不一樣', '邊緣比中心更誠實', '不要一直看中間', '有些東西只在看不清楚時存在', '再往前一步'];
function evWhisper() { whisperEdge(WHISPERS[Math.floor(Math.random() * WHISPERS.length)], 5200); }

function triggerSuspense(name) {
  const now = performance.now();
  if (!name) {
    const hasWall = world.walls.some((w) => w.hits >= 2);
    const pool = [['figure', 3], ['door', hasWall ? 2.5 : 0], ['blackout', 1.5], ['steps', 1.2], ['glitch', 1.3], ['whisper', 1.2]]
      .filter((p) => p[1] > 0 && p[0] !== susp.last && !(p[0] === 'figure' && susp.fig));
    let tot = 0;
    for (const p of pool) tot += p[1];
    let r = Math.random() * tot;
    name = pool[0][0];
    for (const p of pool) { if ((r -= p[1]) <= 0) { name = p[0]; break; } }
  }
  let ok = true;
  if (name === 'figure') ok = evFigure(now);
  else if (name === 'door') ok = evDoor(now);
  else if (name === 'blackout') evBlackout(now);
  else if (name === 'steps') evSteps();
  else if (name === 'glitch') evGlitch(now);
  else if (name === 'whisper') evWhisper();
  if (!ok) { evWhisper(); name = 'whisper'; }
  susp.last = name; susp.count++; susp.lastEv = now;
  if (net.on) netEvent('suspense', { name: ({ figure: '邊緣人影', door: '牆上多了一扇門', blackout: '視野收縮', steps: '腳步聲', glitch: '訊號故障', whisper: '低語' })[name] || name });
  susp.next = now + rand(10000, 17000);
  return name;
}

// ---------- 每格更新 ----------
function updateSuspense(dt, now) {
  const yaw = gameHeading();
  let dy = wrapPi(yaw - susp.prevYaw);
  susp.prevYaw = yaw;
  const rate = dy / Math.max(dt, 1e-3);
  susp.yawAbs += (Math.abs(rate) - susp.yawAbs) * Math.min(1, dt * 0.8);
  if (Math.abs(rate) > 0.4) {
    const sg = rate > 0 ? 1 : -1;
    if (susp.lastSign && sg !== susp.lastSign) susp.rev += 1;
    susp.lastSign = sg;
  }
  susp.rev *= Math.exp(-dt / 4);
  const jit = Math.abs(moveSpeed - susp.prevSpeed) / Math.max(dt, 1e-3);
  susp.prevSpeed = moveSpeed;
  susp.spdJit += (jit - susp.spdJit) * Math.min(1, dt * 0.6);
  susp.erratic = Math.min(1, 0.5 * clamp01(susp.yawAbs / 0.9) + 0.5 * clamp01(susp.rev / 2.5) + 0.3 * clamp01(susp.spdJit / 2));

  if (running && now >= susp.next) {
    const quiet = now - susp.lastEv > 50000;
    if (susp.erratic > 0.38 || (quiet && moveSpeed > 0.3)) triggerSuspense();
  }
  updateFigure(dt, now);
  updateDoor(now);

  // 視野閃爍
  let mul = 1;
  if (susp.flicker) {
    const t = (now - susp.flicker.start) / susp.flicker.dur;
    if (t >= 1) susp.flicker = null;
    else {
      const pulse = Math.sin(t * 38) * Math.sin(t * 17 + 1);
      mul = pulse > 0.15 ? 1 : 0.35;
      if (t > 0.8) mul = lerp(mul, 1, (t - 0.8) / 0.2);
    }
  }
  susp.fovMul = mul;
}

// ---------- 場景內的繪製（畫進鏡頭影像層，會被視野規則處理） ----------
function figSegs(f, now) {
  // 以使用者視線為正面的看板式火柴人（略高於常人），單位公尺
  const dx = f.x - pos.x, dz = f.z - pos.z, d = Math.hypot(dx, dz) || 1;
  const rx = -dz / d, rz = dx / d;
  const sc = 1.12;
  const sway = Math.sin(now / 900 + f.seed) * 0.03;
  const P = (s, y) => [f.x + rx * (s + sway * y) * sc, y * sc, f.z + rz * (s + sway * y) * sc];
  const segs = [];
  const L = (a, b) => segs.push([a[0], a[1], a[2], b[0], b[1], b[2]]);
  const head = [];
  for (let i = 0; i < 8; i++) { const a = (i / 8) * Math.PI * 2; head.push(P(Math.cos(a) * 0.1, 1.62 + Math.sin(a) * 0.12)); }
  for (let i = 0; i < 8; i++) L(head[i], head[(i + 1) % 8]);
  L(P(0, 1.5), P(0, 0.95));
  L(P(-0.2, 1.42), P(0.2, 1.42));
  L(P(-0.2, 1.42), P(-0.26, 0.98)); L(P(-0.26, 0.98), P(-0.22, 0.72));
  L(P(0.2, 1.42), P(0.26, 0.98)); L(P(0.26, 0.98), P(0.22, 0.72));
  L(P(-0.12, 0.95), P(0.12, 0.95));
  L(P(-0.12, 0.95), P(-0.13, 0.48)); L(P(-0.13, 0.48), P(-0.12, 0));
  L(P(0.12, 0.95), P(0.13, 0.48)); L(P(0.13, 0.48), P(0.12, 0));
  return segs;
}

function drawSuspScene(c, now) {
  const near = 0.15;
  const strokeSegs = (segs, alpha, lw) => {
    c.strokeStyle = `rgba(255,255,255,${alpha.toFixed(2)})`;
    c.lineWidth = lw;
    c.beginPath();
    for (const sg of segs) seg3(c, sg[0], sg[1], sg[2], sg[3], sg[4], sg[5]);
    c.stroke();
  };
  const f = susp.fig;
  if (f) {
    let a = clamp01((now - f.born) / 500);
    if (f.vanish) a *= 1 - clamp01((now - f.vanish) / 500);
    if (Math.sin(now / 70 + f.seed) > 0.92) a *= 0.3; // 閃爍
    if (a > 0.02) strokeSegs(figSegs(f, now), 0.95 * a, 2.2);
  }
  const d = susp.door;
  if (d) {
    const c0 = Math.cos(d.rot), s0 = Math.sin(d.rot);
    const W2 = 0.475, HH = 2.1;
    const lp = (lx, y, lz) => [d.x + lx * c0 - lz * s0, y, d.z + lx * s0 + lz * c0];
    const open = d.closeAt ? 1 - clamp01((now - d.closeAt) / 700) : clamp01((now - d.born) / 2200);
    const ang = open * 0.75; // 開啟角度（弧度）
    const segs = [];
    const L = (a, b) => segs.push([a[0], a[1], a[2], b[0], b[1], b[2]]);
    const g = clamp01((now - d.born) / 900) * (d.closeAt ? open : 1);
    const sy = HH * g;
    L(lp(-W2, 0, 0), lp(-W2, sy, 0)); L(lp(W2, 0, 0), lp(W2, sy, 0)); L(lp(-W2, sy, 0), lp(W2, sy, 0));
    // 門板：以左側為軸，往建立時使用者所在的一側打開（局部 z 軸 = (-sin, cos)）
    const zdir = (d.nx * -s0 + d.nz * c0) >= 0 ? 1 : -1;
    const ex = -W2 + Math.cos(ang) * 2 * W2, ez2 = zdir * Math.sin(ang) * 2 * W2;
    L(lp(-W2, 0, 0), lp(ex, 0, ez2)); L(lp(-W2, sy, 0), lp(ex, sy, ez2)); L(lp(ex, 0, ez2), lp(ex, sy, ez2));
    L(lp(-W2, 0, 0), lp(ex, sy, ez2));
    strokeSegs(segs, 0.9 * (Math.sin(now / 90) > 0.9 ? 0.4 : 1), 2);
    // 門縫漏出的光：從門框底部往使用者側的地面扇形展開
    const fan = [];
    for (let i = -2; i <= 2; i++) {
      const lx = i * 0.2, t = 1.8 * open * g;
      fan.push([...lp(lx, 0.01, 0), ...lp(lx + i * 0.5, 0.01, zdir * t)]);
    }
    strokeSegs(fan, 0.4 * open, 1.2);
  }
}

// ---------- 畫面上方的覆蓋層（故障、閃光、字幕、邊緣低語） ----------
function drawSuspOverlay(now) {
  ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  if (now < susp.glitchUntil) {
    const n = 4 + Math.floor(Math.random() * 4);
    for (let i = 0; i < n; i++) {
      const sh = rand(0.02, 0.09) * H, sy = rand(0, H - sh), off = rand(-0.09, 0.09) * W;
      ctx.drawImage(cv, 0, sy * DPR, W * DPR, sh * DPR, off, sy, W, sh);
    }
    ctx.fillStyle = 'rgba(255,255,255,0.06)';
    ctx.fillRect(0, rand(0, H), W, 2);
  }
  if (now < susp.flashUntil) {
    ctx.fillStyle = `rgba(0,0,0,${susp.flashA})`;
    ctx.fillRect(0, 0, W, H);
  }
  if (susp.flicker) {
    const t = (now - susp.flicker.start) / susp.flicker.dur;
    if (Math.sin(t * 38) < -0.7) { ctx.fillStyle = 'rgba(0,0,0,0.55)'; ctx.fillRect(0, 0, W, H); }
  }
  if (susp.edge) {
    const e = susp.edge, t = now - e.born, left = e.until - now;
    if (left < 0) susp.edge = null;
    else {
      const a = Math.min(clamp01(t / 700), clamp01(left / 900));
      ctx.font = '13px -apple-system, "PingFang TC", sans-serif';
      ctx.textBaseline = 'middle';
      ctx.fillStyle = `rgba(255,255,255,${(0.75 * a).toFixed(2)})`;
      const jitter = Math.sin(now / 55) * 1.5 * (Math.sin(now / 300) > 0.6 ? 1 : 0);
      ctx.save();
      ctx.translate(e.side < 0 ? 12 : W - 12, e.y * H + jitter);
      ctx.rotate((e.side < 0 ? -1 : 1) * Math.PI / 2);
      ctx.textAlign = 'center';
      ctx.fillText(e.text.split('').join(' '), 0, 0);
      ctx.restore();
    }
  }
  if (susp.sub) {
    const s = susp.sub, left = s.until - now;
    if (left < 0) susp.sub = null;
    else {
      const a = Math.min(clamp01((now - s.born) / 300), clamp01(left / 600));
      ctx.font = '600 15px -apple-system, "PingFang TC", sans-serif';
      ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
      let txt = s.text;
      while (txt.length > 4 && ctx.measureText(txt).width > W - 40) txt = txt.slice(0, -2) + '…';
      const tw = ctx.measureText(txt).width + 24, y = H * 0.62;
      ctx.fillStyle = `rgba(0,0,0,${(0.6 * a).toFixed(2)})`;
      ctx.fillRect(W / 2 - tw / 2, y - 16, tw, 32);
      ctx.fillStyle = `rgba(255,255,255,${a.toFixed(2)})`;
      ctx.fillText(txt, W / 2, y);
    }
  }
}

function resetSuspense() {
  susp.fig = null; susp.door = null; susp.flicker = null; susp.sub = null; susp.edge = null;
  susp.glitchUntil = 0; susp.flashUntil = 0; susp.fovMul = 1; susp.count = 0; susp.last = '';
  susp.rev = 0; susp.yawAbs = 0; susp.spdJit = 0; susp.erratic = 0;
  susp.next = performance.now() + 14000; susp.lastEv = performance.now();
}

// ==========================================================
// 虛實同步：雙點對位（AR 座標系 ↔ 基地 site 座標系）
//   AR 座標系：這個程式的 pos（步伐推算）與 headX/headZ，啟動或校準時定義
//   site 座標系：基地模型（公尺）。這裡內建一個示範基地（房間 + 隔間 + 假門 + 鑰匙）
//   對位：站在基地已知點 A 按一次、走到已知點 B 按一次（A、B 相距 L 公尺，在 site 裡 A=(0,0)、B=(L,0)）
//     旋轉 φ = angle(B_site − A_site) − angle(B_ar − A_ar)
//     p_site = R(φ)·(p_ar − A_ar) + A_site        （剛體轉換，不縮放）
//     尺度比 = L / |B_ar − A_ar|  → 就是「步長」的誤差，可回填修正
//   之後：玩家的 site 座標、朝向、到牆距離（射線）、到物件距離都由同一套座標算出，
//         基地模型畫回 AR 畫面，被模型牆擋住的虛擬物不畫（遮擋）。
// ==========================================================
const al = { state: 0, A: null, B: null, phi: 0, scale: 1, err: 0, ok: false, showSite: true, L: 4.0, ay: 0 };
const alR = { x: 0, z: 0, h: 0, wallD: null, items: [] };

function siteWalls() {
  const L = al.L, X = L + 1.5, Z = -4.5, P = L * 0.5;
  return [
    [0, 0, X, 0], [X, 0, X, Z], [X, Z, 0, Z], [0, Z, 0, 0], // 房間外牆
    [P, Z, P, -2.7], // 隔間
  ];
}
function siteItems() {
  const L = al.L, Z = -4.5, P = L * 0.5;
  return [
    { k: 'door', x: L * 0.62, z: Z, nx: 0, nz: 1, label: '假門（模型有、現實沒有）' },
    { k: 'key', x: P + 0.8, z: -3.8, label: '鑰匙・隔間後' },
    { k: 'key', x: 1.0, z: -2.0, label: '鑰匙・開放處' },
  ];
}

function arToSite(x, z) {
  if (!al.ok) return null;
  const dx = x - al.A.x, dz = z - al.A.z, c = Math.cos(al.phi), s = Math.sin(al.phi);
  return [dx * c - dz * s, dx * s + dz * c];
}
function siteToAR(x, z) {
  if (!al.ok) return null;
  const c = Math.cos(-al.phi), s = Math.sin(-al.phi);
  return [al.A.x + x * c - z * s, al.A.z + x * s + z * c];
}

function alignReset() {
  al.state = 0; al.A = null; al.B = null; al.ok = false; al.scale = 1; al.err = 0;
  updateAlignBtn();
}
function updateAlignBtn() {
  const b = document.getElementById('bAlign');
  if (!b) return;
  b.textContent = ['對位：站A點按我', '走到B點按我', '已對位（重來）'][al.state];
  b.classList.toggle('on', al.state === 2);
}

function alignConfirm() {
  if (!running) return;
  if (al.state === 0) {
    al.A = { x: pos.x, z: pos.z };
    al.state = 1;
    say(`A 點已記錄。請走到 B 點（距 A ${al.L.toFixed(1)} 公尺）再按一次`, 4200);
  } else if (al.state === 1) {
    const d = Math.hypot(pos.x - al.A.x, pos.z - al.A.z);
    if (d < 0.8) { say('離 A 點太近了，請走遠一點再按', 3000); return; }
    al.B = { x: pos.x, z: pos.z };
    const angAR = Math.atan2(al.B.z - al.A.z, al.B.x - al.A.x);
    al.phi = wrapPi(0 - angAR); // site 裡 B 在 +x 方向
    al.scale = al.L / d;
    al.ok = true; al.state = 2;
    // 剛體轉換下 B 的殘差（= 尺度誤差）
    const sb = arToSite(al.B.x, al.B.z);
    al.err = Math.hypot(sb[0] - al.L, sb[1]);
    say(`對位完成：旋轉 ${(al.phi / DEG).toFixed(0)}°，步長尺度 ×${al.scale.toFixed(2)}，B 點殘差 ${al.err.toFixed(2)} m`, 5200);
  } else {
    alignReset();
    say('已清除對位', 1800);
  }
  updateAlignBtn();
}

function applyScale() {
  if (!al.ok) { say('請先完成對位', 2000); return; }
  const k = Math.max(0.5, Math.min(2, al.scale));
  S.stepLen = Math.max(0.3, Math.min(1.2, S.stepLen * k));
  const el = document.getElementById('sStep'), o = document.getElementById('oStep');
  if (el) { el.value = S.stepLen; if (o) o.textContent = S.stepLen.toFixed(2); }
  say(`步長已修正為 ${S.stepLen.toFixed(2)} m；請重新對位`, 3600);
  alignReset();
}

// 射線（平面）對線段
function rayHitSeg(ox, oz, dx, dz, x1, z1, x2, z2) {
  const ex = x2 - x1, ez = z2 - z1;
  const den = dx * ez - dz * ex;
  if (Math.abs(den) < 1e-9) return null;
  const t = ((x1 - ox) * ez - (z1 - oz) * ex) / den;
  const u = ((x1 - ox) * dz - (z1 - oz) * dx) / den;
  return t >= 0 && u >= 0 && u <= 1 ? t : null;
}
function distToSeg(px, pz, x1, z1, x2, z2) {
  const ex = x2 - x1, ez = z2 - z1, l2 = ex * ex + ez * ez || 1;
  const t = Math.max(0, Math.min(1, ((px - x1) * ex + (pz - z1) * ez) / l2));
  return Math.hypot(px - (x1 + ex * t), pz - (z1 + ez * t));
}

// 以偵測到的真實牆（世界模型）遮擋虛擬建築：玩家到物件中心的視線穿過牆就不畫
function hiddenByRealWall(o) {
  for (const w of world.walls) {
    if (w.hits < 3) continue;
    if (distToSeg(o.x, o.z, w.x1, w.z1, w.x2, w.z2) < 0.5) continue;
    if (segCrossAny(pos.x, pos.z, o.x, o.z, w.x1, w.z1, w.x2, w.z2)) return true;
  }
  return false;
}

// ---------- 每格更新：site 座標、朝向、到牆距離、到物件距離 ----------
function updateAlign() {
  if (!al.ok) { alR.wallD = null; alR.items = []; return; }
  const p = arToSite(pos.x, pos.z);
  alR.x = p[0]; alR.z = p[1];
  const hx = headX * Math.cos(al.phi) - headZ * Math.sin(al.phi);
  const hz = headX * Math.sin(al.phi) + headZ * Math.cos(al.phi);
  alR.h = ((Math.atan2(hx, -hz) / DEG) + 360) % 360;
  // 前方牆（site 座標下做射線）
  let best = null;
  for (const w of siteWalls()) {
    const t = rayHitSeg(p[0], p[1], hx, hz, w[0], w[1], w[2], w[3]);
    if (t !== null && (best === null || t < best)) best = t;
  }
  alR.wallD = best;
  alR.items = siteItems().map((it) => {
    const dx = it.x - p[0], dz = it.z - p[1], d = Math.hypot(dx, dz);
    const ux = dx / (d || 1), uz = dz / (d || 1);
    let hidden = false;
    for (const w of siteWalls()) {
      if (segCrossAny(p[0], p[1], it.x - ux * 0.06, it.z - uz * 0.06, w[0], w[1], w[2], w[3])) { hidden = true; break; }
    }
    const rel = wrapPi(Math.atan2(dx, -dz) - Math.atan2(hx, -hz));
    return { it, d, hidden, rel };
  });
}

// ---------- 基地模型畫回 AR（畫進影像層） ----------
function drawSite(c, now) {
  if (!al.ok || !al.showSite) return;
  c.lineJoin = 'round';
  c.strokeStyle = 'rgba(255,205,90,0.8)';
  c.lineWidth = 1.6;
  c.beginPath();
  for (const w of siteWalls()) {
    const a = siteToAR(w[0], w[1]), b = siteToAR(w[2], w[3]);
    seg3(c, a[0], 0, a[1], b[0], 0, b[1]);
    seg3(c, a[0], SITE_H, a[1], b[0], SITE_H, b[1]);
    seg3(c, a[0], 0, a[1], a[0], SITE_H, a[1]);
    seg3(c, b[0], 0, b[1], b[0], SITE_H, b[1]);
    const len = Math.hypot(w[2] - w[0], w[3] - w[1]);
    for (let s = 1.2; s < len - 0.4; s += 1.2) {
      const t = s / len, x = lerp(a[0], b[0], t), z = lerp(a[1], b[1], t);
      seg3(c, x, 0, z, x, SITE_H, z);
    }
  }
  c.stroke();
  for (const r of alR.items) {
    if (r.hidden) continue; // 被模型牆擋住：遮擋
    const it = r.it, p = siteToAR(it.x, it.z);
    c.strokeStyle = it.k === 'door' ? 'rgba(255,120,90,0.95)' : 'rgba(120,230,255,0.95)';
    c.lineWidth = 2;
    c.beginPath();
    if (it.k === 'door') {
      const a = siteToAR(it.x - 0.475, it.z), b = siteToAR(it.x + 0.475, it.z);
      seg3(c, a[0], 0, a[1], a[0], 2.1, a[1]);
      seg3(c, b[0], 0, b[1], b[0], 2.1, b[1]);
      seg3(c, a[0], 2.1, a[1], b[0], 2.1, b[1]);
    } else {
      const y = 1.1 + Math.sin(now / 500) * 0.06, q = 0.16;
      const top = [p[0], y + q, p[1]], bot = [p[0], y - q, p[1]];
      const ring = [[q, 0], [0, q], [-q, 0], [0, -q]].map((o) => [p[0] + o[0], y, p[1] + o[1]]);
      for (let i = 0; i < 4; i++) {
        const n = ring[(i + 1) % 4];
        seg3(c, ring[i][0], ring[i][1], ring[i][2], n[0], n[1], n[2]);
        seg3(c, top[0], top[1], top[2], ring[i][0], ring[i][1], ring[i][2]);
        seg3(c, bot[0], bot[1], bot[2], ring[i][0], ring[i][1], ring[i][2]);
      }
    }
    c.stroke();
  }
}

// ---------- 覆蓋層：物件標籤、站位文字、小地圖 ----------
function drawAlignOverlay() {
  ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  const bar = document.getElementById('bar');
  const bottom = (bar && !bar.hidden ? bar.getBoundingClientRect().top : H - 76) - 8;
  const MS = Math.min(120, Math.max(90, Math.min(W, H) * 0.28));
  const x0 = 8, y0 = bottom - MS;
  const lines = [];
  if (!al.ok) {
    lines.push(al.state === 0 ? '未對位：站在已知點 A 按「對位」' : '請走到 B 點再按一次');
  } else {
    lines.push(`site 位置 (${alR.x.toFixed(2)}, ${alR.z.toFixed(2)}) m　朝向 ${alR.h.toFixed(0)}°`);
    lines.push(`前方牆 ${alR.wallD === null ? '—' : alR.wallD.toFixed(2) + ' m'}　尺度 ×${al.scale.toFixed(2)}`);
    const keys = alR.items.filter((r) => r.it.k === 'key').sort((p, q) => p.d - q.d);
    if (keys[0]) lines.push(`最近鑰匙 ${keys[0].d.toFixed(1)} m ${keys[0].hidden ? '（被牆擋住）' : ''}`);
  }
  ctx.font = '11px ui-monospace, Menlo, monospace';
  ctx.textAlign = 'left'; ctx.textBaseline = 'top';
  let w = 0;
  for (const t of lines) w = Math.max(w, ctx.measureText(t).width);
  const ty = y0 - 6 - lines.length * 15;
  ctx.fillStyle = 'rgba(0,0,0,0.55)';
  ctx.fillRect(x0, ty - 3, w + 14, lines.length * 15 + 6);
  ctx.fillStyle = 'rgba(255,230,160,0.95)';
  lines.forEach((t, i) => ctx.fillText(t, x0 + 7, ty + i * 15));

  // 小地圖（site 平面）
  const L = al.L, minx = -0.6, maxx = L + 2.1, minz = -5.1, maxz = 0.6;
  const s = Math.min(MS / (maxx - minx), MS / (maxz - minz));
  const mx = (x) => x0 + (x - minx) * s, mz = (z) => y0 + (z - minz) * s;
  ctx.fillStyle = 'rgba(0,0,0,0.55)'; ctx.fillRect(x0, y0, MS, MS);
  ctx.strokeStyle = 'rgba(255,255,255,0.3)'; ctx.strokeRect(x0 + 0.5, y0 + 0.5, MS, MS);
  ctx.save();
  ctx.beginPath(); ctx.rect(x0, y0, MS, MS); ctx.clip();
  ctx.strokeStyle = 'rgba(255,205,90,0.9)'; ctx.lineWidth = 1.5;
  ctx.beginPath();
  for (const wl of siteWalls()) { ctx.moveTo(mx(wl[0]), mz(wl[1])); ctx.lineTo(mx(wl[2]), mz(wl[3])); }
  ctx.stroke();
  for (const it of siteItems()) {
    ctx.fillStyle = it.k === 'door' ? 'rgba(255,120,90,0.95)' : 'rgba(120,230,255,0.95)';
    ctx.beginPath(); ctx.arc(mx(it.x), mz(it.z), 2.5, 0, Math.PI * 2); ctx.fill();
  }
  ctx.font = '10px ui-monospace, Menlo, monospace'; ctx.fillStyle = '#fff';
  ctx.fillText('A', mx(0) + 3, mz(0) + 2); ctx.fillText('B', mx(L) - 3, mz(0) + 2);
  if (al.ok) {
    const px = mx(alR.x), pz = mz(alR.z), a = alR.h * DEG;
    ctx.fillStyle = '#fff';
    ctx.beginPath();
    ctx.moveTo(px + Math.sin(a) * 6, pz - Math.cos(a) * 6);
    ctx.lineTo(px + Math.sin(a + 2.5) * 5, pz - Math.cos(a + 2.5) * 5);
    ctx.lineTo(px + Math.sin(a - 2.5) * 5, pz - Math.cos(a - 2.5) * 5);
    ctx.closePath(); ctx.fill();
  }
  ctx.restore();

  // 物件標籤（畫在主畫布，不受視野限制）
  if (al.ok && al.showSite) {
    ctx.textAlign = 'center'; ctx.textBaseline = 'bottom';
    ctx.font = '12px -apple-system, "PingFang TC", sans-serif';
    for (const r of alR.items) {
      if (r.hidden) continue;
      const p = siteToAR(r.it.x, r.it.z);
      const c = toCam(p[0] - pos.x, (r.it.k === 'door' ? 2.3 : 1.4) - EYE, p[1] - pos.z);
      if (c[2] < 0.3) continue;
      const sp = toScreen(c);
      if (sp[0] < 0 || sp[0] > W || sp[1] < 0 || sp[1] > H) continue;
      ctx.fillStyle = 'rgba(0,0,0,0.55)';
      const t = `${r.it.label}　${r.d.toFixed(1)} m`, tw = ctx.measureText(t).width + 10;
      ctx.fillRect(sp[0] - tw / 2, sp[1] - 18, tw, 18);
      ctx.fillStyle = '#fff'; ctx.fillText(t, sp[0], sp[1] - 3);
    }
  }
}
const SITE_H = 2.6;

// ==========================================================
// 物體辨識（快速層，完全在手機上跑，不需要金鑰）
//   模型：TensorFlow.js + COCO-SSD（在大量網路圖片資料集 COCO 上訓練的偵測模型，約 80 類）
//   流程：影格 → 偵測（類別、框）→ 框底落在地面 → 用眼高與俯仰角算距離 → AR 座標 →
//         世界模型旁的「物件記憶」→ 知識庫（材質、用途、可能性、遊戲用途）→ 生成錨點
//   限制：COCO 沒有「門」「牆」類別（牆、柱、轉角仍由幾何偵測負責）；人不處理、不記錄
//         材質與可能性來自內建知識庫（常見情況），不是看影像判斷的；要看影像判斷需要深度層（雲端視覺語言模型）
// ==========================================================
const OKB = {
  chair: { zh: '椅子', mat: ['木或塑膠', '金屬骨架', '坐墊多為織物'], uses: ['坐', '放置物品'], aff: ['可作低矮掩體', '可移動成路障', '可站上去看高處'], role: 'cover', h: 0.9, w: 0.5 },
  couch: { zh: '沙發', mat: ['織物或皮革', '木框'], uses: ['坐', '躺'], aff: ['可作大型掩體', '後方可藏物', '坐墊下可藏線索'], role: 'cover', h: 0.85, w: 1.8 },
  bed: { zh: '床', mat: ['織物', '木或金屬床架'], uses: ['睡眠'], aff: ['可作大型掩體', '床底可藏物'], role: 'cover', h: 0.6, w: 1.5 },
  'dining table': { zh: '桌子', mat: ['木、板材或玻璃', '金屬桌腳'], uses: ['用餐', '工作', '放置物品'], aff: ['可作遮蔽', '桌面可放線索', '桌下可藏身'], role: 'cover', h: 0.75, w: 1.2 },
  tv: { zh: '電視／螢幕', mat: ['塑膠外殼', '玻璃面板'], uses: ['顯示影像'], aff: ['可顯示線索', '關閉時是黑色反光面', '會發光'], role: 'clue', h: 0.6, w: 0.9 },
  laptop: { zh: '筆電', mat: ['金屬或塑膠', '玻璃螢幕'], uses: ['工作', '連網'], aff: ['可顯示線索', '可作密碼輸入處'], role: 'clue', h: 0.25, w: 0.35 },
  keyboard: { zh: '鍵盤', mat: ['塑膠'], uses: ['輸入'], aff: ['可作密碼輸入處'], role: 'clue', h: 0.05, w: 0.45 },
  mouse: { zh: '滑鼠', mat: ['塑膠'], uses: ['操作電腦'], aff: ['小型可拾取物'], role: 'item', h: 0.04, w: 0.07 },
  'cell phone': { zh: '手機', mat: ['玻璃與金屬'], uses: ['通訊'], aff: ['可顯示線索', '小型可拾取物'], role: 'item', h: 0.01, w: 0.07 },
  book: { zh: '書', mat: ['紙'], uses: ['閱讀'], aff: ['可夾藏線索', '可拾取'], role: 'item', h: 0.03, w: 0.2 },
  bottle: { zh: '瓶子', mat: ['塑膠或玻璃'], uses: ['裝液體'], aff: ['可拾取', '可作訊號物'], role: 'item', h: 0.25, w: 0.07 },
  cup: { zh: '杯子', mat: ['陶瓷、玻璃或塑膠'], uses: ['喝飲料'], aff: ['可拾取', '可作訊號物'], role: 'item', h: 0.1, w: 0.08 },
  'potted plant': { zh: '盆栽', mat: ['植物', '陶或塑膠盆'], uses: ['裝飾'], aff: ['可作矮掩體', '盆下可藏物'], role: 'cover', h: 0.7, w: 0.4 },
  refrigerator: { zh: '冰箱', mat: ['金屬外殼'], uses: ['冷藏'], aff: ['可作大型掩體', '門可作機關'], role: 'cover', h: 1.8, w: 0.7 },
  microwave: { zh: '微波爐', mat: ['金屬與塑膠'], uses: ['加熱'], aff: ['門可作機關', '內部可藏物'], role: 'clue', h: 0.3, w: 0.5 },
  oven: { zh: '烤箱', mat: ['金屬'], uses: ['烹調'], aff: ['門可作機關'], role: 'clue', h: 0.6, w: 0.6 },
  sink: { zh: '水槽', mat: ['不鏽鋼或陶瓷'], uses: ['洗滌'], aff: ['水聲可作線索'], role: 'clue', h: 0.9, w: 0.6 },
  toilet: { zh: '馬桶', mat: ['陶瓷'], uses: ['衛生'], aff: ['隔間可作掩蔽'], role: 'item', h: 0.4, w: 0.4 },
  clock: { zh: '時鐘', mat: ['塑膠或金屬'], uses: ['報時'], aff: ['可作時間謎題'], role: 'clue', h: 0.3, w: 0.3 },
  vase: { zh: '花瓶', mat: ['陶瓷或玻璃'], uses: ['裝飾'], aff: ['可藏物', '易碎訊號'], role: 'item', h: 0.3, w: 0.15 },
  backpack: { zh: '背包', mat: ['織物'], uses: ['攜帶物品'], aff: ['可藏物', '可作小型掩體'], role: 'item', h: 0.5, w: 0.3 },
  suitcase: { zh: '行李箱', mat: ['塑膠或織物'], uses: ['運送'], aff: ['可作矮掩體', '可上鎖藏物'], role: 'cover', h: 0.65, w: 0.45 },
  bench: { zh: '長椅', mat: ['木或金屬'], uses: ['坐'], aff: ['可作低矮掩體', '可作路障'], role: 'cover', h: 0.5, w: 1.4 },
  umbrella: { zh: '雨傘', mat: ['織物與金屬'], uses: ['遮雨'], aff: ['可拾取'], role: 'item', h: 0.8, w: 0.1 },
};
const ob = { on: false, loading: false, ready: false, model: null, busy: false, last: 0, status: '關閉', boxes: [], boxesAt: 0, card: null, passes: 0, ms: 0 };
const omem = [];
let omemId = 1;

function loadScript(src) {
  return new Promise((res, rej) => {
    const s = document.createElement('script');
    s.src = src; s.onload = res; s.onerror = () => rej(new Error('無法載入 ' + src.split('/').slice(-2).join('/')));
    document.head.appendChild(s);
  });
}

// 載入模型（人物偵測與物體辨識共用）
async function ensureModel() {
  if (ob.ready || ob.loading) return;
  ob.loading = true; ob.status = '載入模型中（需要網路，約 5–10 MB）';
  try {
    if (!window.tf) await loadScript('https://cdn.jsdelivr.net/npm/@tensorflow/tfjs@4.22.0/dist/tf.min.js');
    if (!window.cocoSsd) await loadScript('https://cdn.jsdelivr.net/npm/@tensorflow-models/coco-ssd@2.2.3/dist/coco-ssd.min.js');
    ob.model = await window.cocoSsd.load({ base: 'lite_mobilenet_v2' });
    ob.ready = true; ob.status = ob.on ? '辨識中' : '待命';
  } catch (e) {
    ob.status = '載入失敗：' + (e && e.message ? e.message : e);
  }
  ob.loading = false;
}

async function toggleObjects() {
  if (ob.on) { ob.on = false; ob.status = ob.ready ? '待命' : '關閉'; ob.boxes = []; return; }
  ob.on = true;
  await ensureModel();
  if (!ob.ready) ob.on = false; else ob.status = '辨識中';
}

function withPose(snap, fn) {
  const sB = B, sx = pos.x, sz = pos.z, sf = FPX;
  B = snap.B; pos.x = snap.px; pos.z = snap.pz; FPX = snap.fpx;
  try { return fn(); } finally { B = sB; pos.x = sx; pos.z = sz; FPX = sf; }
}

function runObjects(now) {
  if (!running || !(ob.on || S.people) || !ob.ready || !ob.model || ob.busy || now - ob.last < 450 || angSpeed > 1.2) return;
  if (!(video.videoWidth && video.readyState >= 2)) return;
  ob.busy = true; ob.last = now;
  const snap = { B, px: pos.x, pz: pos.z, fpx: FPX, vw: video.videoWidth, vh: video.videoHeight, W, H, t: now };
  const t0 = performance.now();
  ob.model.detect(video, 12, 0.45).then((preds) => {
    ob.ms += (performance.now() - t0 - ob.ms) * 0.3;
    processDetections(preds, snap);
  }).catch((e) => { ob.status = '辨識錯誤：' + (e && e.message ? e.message : e); })
    .finally(() => { ob.busy = false; });
}

// preds: [{class, score, bbox:[x,y,w,h]}]（影像像素座標）；snap：送出辨識當下的姿態
function processDetections(preds, snap) {
  const now = performance.now();
  if (S.people) ppIngest(preds, snap);
  if (!ob.on) { ob.boxes = []; return; }
  const s = Math.max(snap.W / snap.vw, snap.H / snap.vh);
  const ox = (snap.W - snap.vw * s) / 2, oy = (snap.H - snap.vh * s) / 2;
  const boxes = [];
  world_seen: {
    const seen = new Set();
    for (const p of preds) {
      const kb = OKB[p.class];
      if (!kb) continue; // 含 person：不處理、不記錄
      const bx = ox + p.bbox[0] * s, by = oy + p.bbox[1] * s, bw = p.bbox[2] * s, bh = p.bbox[3] * s;
      const fp = withPose(snap, () => floorPoint(bx + bw / 2, by + bh));
      const box = { x: bx, y: by, w: bw, h: bh, cls: p.class, zh: kb.zh, score: p.score, d: fp ? fp.d : null, o: null };
      boxes.push(box);
      if (!fp || fp.d < 0.6 || fp.d > 9) continue;
      const wm = Math.min(3, Math.max(0.05, (bw / snap.fpx) * fp.d));
      // 融合到物件記憶
      let best = null, bd = 0.8;
      for (const o of omem) {
        if (o.cls !== p.class) continue;
        const d = Math.hypot(o.x - fp.x, o.z - fp.z);
        if (d < bd) { bd = d; best = o; }
      }
      if (!best) {
        best = { id: omemId++, cls: p.class, zh: kb.zh, kb, role: kb.role, x: fp.x, z: fp.z, w: wm, hits: 0, miss: 0, score: 0, used: 0, born: now };
        omem.push(best);
      } else {
        best.x += (fp.x - best.x) * 0.3; best.z += (fp.z - best.z) * 0.3; best.w += (wm - best.w) * 0.2;
      }
      best.hits = Math.min(best.hits + 1, 30); best.miss = 0; best.score = Math.max(best.score * 0.8, p.score); best.last = now;
      seen.add(best.id);
      box.o = best;
    }
    // 在視野內卻沒被偵測到的，慢慢扣分
    for (const o of omem) {
      if (seen.has(o.id)) continue;
      if (!inView(o.x, o.z, 22 * DEG)) continue;
      if (++o.miss > 6) { o.hits -= 1; o.miss = 0; }
    }
    for (let i = omem.length - 1; i >= 0; i--) if (omem[i].hits <= 0) omem.splice(i, 1);
  }
  ob.boxes = boxes; ob.boxesAt = now; ob.passes++;
  ob.status = `辨識中　${boxes.length} 個物體`;
}

function clearObjects() { omem.length = 0; ob.boxes = []; ob.card = null; }

// ---------- AR 內的呈現：物件佔位框（黃綠色） ----------
function drawObjects(c) {
  c.lineJoin = 'round';
  for (const o of omem) {
    if (o.hits < 2) continue;
    const kb = o.kb, w = Math.max(0.1, Math.min(o.w, kb.w * 1.6)) / 2, h = kb.h;
    const al = Math.min(0.9, 0.35 + o.hits * 0.06);
    c.strokeStyle = `rgba(190,255,120,${al.toFixed(2)})`;
    c.lineWidth = 1.6;
    c.beginPath();
    for (const y of [0, h]) {
      seg3(c, o.x - w, y, o.z - w, o.x + w, y, o.z - w); seg3(c, o.x + w, y, o.z - w, o.x + w, y, o.z + w);
      seg3(c, o.x + w, y, o.z + w, o.x - w, y, o.z + w); seg3(c, o.x - w, y, o.z + w, o.x - w, y, o.z - w);
    }
    for (const q of [[-w, -w], [w, -w], [w, w], [-w, w]]) seg3(c, o.x + q[0], 0, o.z + q[1], o.x + q[0], h, o.z + q[1]);
    c.stroke();
  }
}

// ---------- 覆蓋層：偵測框、標籤、點選卡片 ----------
function drawObjOverlay(now) {
  if (!ob.on || !S.showDet) return; // 偵測框屬於後台資訊，預設不顯示
  ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  if (now - ob.boxesAt < 700) {
    ctx.lineWidth = 1.5;
    ctx.font = '12px -apple-system, "PingFang TC", sans-serif';
    ctx.textAlign = 'left'; ctx.textBaseline = 'bottom';
    for (const b of ob.boxes) {
      ctx.strokeStyle = 'rgba(190,255,120,0.9)';
      ctx.strokeRect(b.x, b.y, b.w, b.h);
      const t = `${b.zh} ${Math.round(b.score * 100)}%${b.d ? '　' + b.d.toFixed(1) + 'm' : ''}`;
      const tw = ctx.measureText(t).width + 8;
      ctx.fillStyle = 'rgba(0,0,0,0.6)'; ctx.fillRect(b.x, b.y - 17, tw, 17);
      ctx.fillStyle = 'rgba(190,255,120,1)'; ctx.fillText(t, b.x + 4, b.y - 3);
    }
  }
  const c = ob.card;
  if (c && now < c.until) {
    const bar = document.getElementById('bar');
    const bottom = (bar && !bar.hidden ? bar.getBoundingClientRect().top : H - 76) - 8;
    const cw = Math.min(W - 16, Math.max(240, W - 150));
    const k = c.kb;
    const lines = [
      `${k.zh}　${c.d != null ? c.d.toFixed(1) + ' m' : ''}　可信度 ${Math.round(c.score * 100)}%`,
      `材質：${k.mat.join('、')}`,
      `用途：${k.uses.join('、')}`,
      `可能性：${k.aff.join('；')}`,
      `遊戲用途：${{ cover: '掩體錨點', clue: '線索顯示處', item: '可拾取物', barrier: '路障' }[k.role] || k.role}`,
      '（材質與用途為常見情況的知識庫，不是看影像判斷）',
    ];
    ctx.font = '12px -apple-system, "PingFang TC", sans-serif';
    const wrap = [];
    for (const ln of lines) {
      let cur = '';
      for (const ch of ln) {
        if (ctx.measureText(cur + ch).width > cw - 20) { wrap.push(cur); cur = ch; } else cur += ch;
      }
      wrap.push(cur);
    }
    const ch = wrap.length * 16 + 14, x = W - cw - 8, y = bottom - ch;
    ctx.fillStyle = 'rgba(0,0,0,0.72)'; ctx.fillRect(x, y, cw, ch);
    ctx.strokeStyle = 'rgba(190,255,120,0.8)'; ctx.strokeRect(x + 0.5, y + 0.5, cw, ch);
    ctx.textAlign = 'left'; ctx.textBaseline = 'top';
    wrap.forEach((t, i) => { ctx.fillStyle = i === 0 ? 'rgba(190,255,120,1)' : 'rgba(255,255,255,0.92)'; ctx.fillText(t, x + 10, y + 7 + i * 16); });
  }
}

function tapObjects(px, py) {
  if (!ob.on || !S.showDet) return false;
  const now = performance.now();
  if (now - ob.boxesAt > 1500) return false;
  for (const b of ob.boxes) {
    if (px >= b.x && px <= b.x + b.w && py >= b.y && py <= b.y + b.h) {
      ob.card = { kb: OKB[b.cls], d: b.d, score: b.score, until: now + 7000 };
      return true;
    }
  }
  return false;
}

// ==========================================================
// 掃描次數 → 周邊點雲密度
//   把四周方向切成 6°×6° 的格子（方位 60 × 俯仰 30）。每次某個方向掉進「中央清晰區」並停留，
//   該格的掃描次數 +1（同一格離開 1 秒以上再進來才算新的一次）。
//   周邊的白色點雲密度 = 0.2 + 0.8 × min(1, 次數 ÷ 5)：中央區看過越多次的方向，轉頭時它在周邊的點雲越密；
//   從沒用中央區看過的方向，只剩稀疏的點。
// ==========================================================
const SC_AZ = 60, SC_EL = 30, SC_FULL = 5;
const sc = { cnt: new Uint8Array(SC_AZ * SC_EL), last: new Float64Array(SC_AZ * SC_EL), seen: 0 };

function scBin(px, py) {
  const r = rayW(px, py), l = Math.hypot(r[0], r[1], r[2]) || 1;
  const az = Math.atan2(r[0], -r[2]), el = Math.asin(Math.max(-1, Math.min(1, r[1] / l)));
  const i = Math.min(SC_AZ - 1, Math.max(0, Math.floor(((az + Math.PI) / (2 * Math.PI)) * SC_AZ)));
  const j = Math.min(SC_EL - 1, Math.max(0, Math.floor(((el + Math.PI / 2) / Math.PI) * SC_EL)));
  return j * SC_AZ + i;
}

function scUpdate(now) {
  if (!running || !S.limitOn) return;
  const st = 26;
  for (let y = C.t + st / 2; y < C.b; y += st) {
    for (let x = C.l + st / 2; x < C.r; x += st) {
      const b = scBin(x, y);
      if (now - sc.last[b] > 1000) { if (sc.cnt[b] < 255) { if (sc.cnt[b] === 0) sc.seen++; sc.cnt[b]++; } }
      sc.last[b] = now;
    }
  }
}

function scMul(px, py) {
  const c = sc.cnt[scBin(px, py)];
  return 0.2 + 0.8 * Math.min(1, c / SC_FULL);
}

function scReset() { sc.cnt.fill(0); sc.last.fill(0); sc.seen = 0; }

// ==========================================================
// 標記物（定位與地圖擴張的錨點）
//   生成：系統在掃描到的牆與柱上自動生成。位置挑「Canny 邊緣的距離變換」最大處——也就是牆面上
//         離任何邊緣（門框、踢腳板、插座、陰影交界）最遠、最平整的一塊——再貼合到牆面平面
//         （法向量＝牆法向、離牆 1.2 cm，四角沿牆切線與鉛直方向展開），所以標記「平貼在牆上」。
//   編號：伺服器依區域編號（A-1、A-2…；4.5 m 內沿用同一字母）。沒連線時本機自己編。
//   偵測：必須走近（≤ 1.5 m）、面對標記、且標記落在「中央清晰區」內，停留約 0.7 秒才算掃描到。
//         離得遠（> 3.2 m）畫面上完全看不到，只在羅盤雷達與指揮端地圖上有點。
//   啟用：回報伺服器；指揮端地圖把它標成已啟用。別人建立的標記被你掃描時，用它修正你的位置（見 mkFix）。
//   座標：已對位 → site 座標（所有玩家共用）；未對位 → AR 座標（只有自己看得到，不上傳）。
// 限制：標記是畫在 AR 裡的「虛擬標記」，位置來自單眼估距的牆（誤差約 10–20%），不是真正貼在牆上的實體碼。
// ==========================================================
const MK_SIZE = 0.3, MK_SEE = 3.2, MK_ACT = 1.5, MK_MAX = 40, MK_HOLD = 0.7;
const mk = { list: [], lid: 1, nextGen: 0, prog: 0, cur: null, localLetters: new Map(), info: '', fix: null, lastWalls: 0, dtAt: 0, dt: new Float32Array(1), created: 0 };

function mkRot(v0, v1, a) { const c = Math.cos(a), s = Math.sin(a); return [v0 * c - v1 * s, v0 * s + v1 * c]; }

// Canny 邊緣的距離變換（8 鄰域近似歐氏距離）：每格到最近邊緣像素的距離（單位：偵測格）
function mkDT() {
  const n = DW * DH;
  if (mk.dtAt === cn.at && mk.dt.length === n) return mk.dt;
  if (mk.dt.length !== n) mk.dt = new Float32Array(n);
  const d = mk.dt, INF = 1e4, R2 = 1.4142;
  for (let k = 0; k < n; k++) d[k] = cmask[k] ? 0 : INF;
  for (let j = 0; j < DH; j++) {
    for (let i = 0; i < DW; i++) {
      const k = j * DW + i;
      let v = d[k];
      if (i > 0) v = Math.min(v, d[k - 1] + 1);
      if (j > 0) {
        v = Math.min(v, d[k - DW] + 1);
        if (i > 0) v = Math.min(v, d[k - DW - 1] + R2);
        if (i < DW - 1) v = Math.min(v, d[k - DW + 1] + R2);
      }
      d[k] = v;
    }
  }
  for (let j = DH - 1; j >= 0; j--) {
    for (let i = DW - 1; i >= 0; i--) {
      const k = j * DW + i;
      let v = d[k];
      if (i < DW - 1) v = Math.min(v, d[k + 1] + 1);
      if (j < DH - 1) {
        v = Math.min(v, d[k + DW] + 1);
        if (i < DW - 1) v = Math.min(v, d[k + DW + 1] + R2);
        if (i > 0) v = Math.min(v, d[k + DW - 1] + R2);
      }
      d[k] = v;
    }
  }
  mk.dtAt = cn.at;
  return d;
}

// ---------- 遮擋用：線段對盒子、線段對線段 ----------
function segBoxEntry(ox, oz, tx, tz, o, pad) {
  const r = o.rot || 0, c = Math.cos(r), s = Math.sin(r);
  const ax = ox - o.x, az = oz - o.z, bx = tx - o.x, bz = tz - o.z;
  const p = [ax * c + az * s, -ax * s + az * c], q = [bx * c + bz * s, -bx * s + bz * c];
  const lo = [-o.w / 2 - pad, -o.d / 2 - pad], hi = [o.w / 2 + pad, o.d / 2 + pad];
  let t0 = 0, t1 = 1;
  for (let k = 0; k < 2; k++) {
    const d = q[k] - p[k];
    if (Math.abs(d) < 1e-9) { if (p[k] < lo[k] || p[k] > hi[k]) return null; }
    else {
      let a = (lo[k] - p[k]) / d, b = (hi[k] - p[k]) / d;
      if (a > b) { const t = a; a = b; b = t; }
      t0 = Math.max(t0, a); t1 = Math.min(t1, b);
      if (t0 > t1) return null;
    }
  }
  return t0;
}
function segT(ax, az, bx, bz, cx, cz, dx, dz) { // a→b 與 c→d 相交時，回傳在 a→b 上的比例
  const d1x = bx - ax, d1z = bz - az, d2x = dx - cx, d2z = dz - cz;
  const den = d1x * d2z - d1z * d2x;
  if (Math.abs(den) < 1e-9) return null;
  const t = ((cx - ax) * d2z - (cz - az) * d2x) / den;
  const u = ((cx - ax) * d1z - (cz - az) * d1x) / den;
  return t >= 0 && t <= 1 && u >= 0 && u <= 1 ? t : null;
}

// 站在 pos 看向 (tx,tz)：被虛擬建築、真實牆、基地模型牆、辨識到的物體擋住的程度。
// 回傳「目標處可見的最低高度」hv：0＝完全看得到；≥ 目標高度＝完全被擋。
function visibleFloor(tx, tz, skipWall) {
  const ox = pos.x, oz = pos.z, dT = Math.hypot(tx - ox, tz - oz);
  if (dT < 0.3) return 0;
  let hv = 0;
  const occl = (t, h) => {
    const v = EYE + (h - EYE) * dT / Math.max(t * dT, 0.05);
    if (v > hv) hv = v;
  };
  for (const o of obs) {
    if (o.dying) continue;
    const t = segBoxEntry(ox, oz, tx, tz, o, 0);
    if (t !== null) occl(t, o.h);
  }
  for (const w of world.walls) {
    if (w.hits < 3 || w === skipWall) continue;
    if (distToSeg(tx, tz, w.x1, w.z1, w.x2, w.z2) < 0.6) continue; // 目標貼著這面牆：不算被它擋
    const t = segT(ox, oz, tx, tz, w.x1, w.z1, w.x2, w.z2);
    if (t !== null) occl(t, 2.6);
  }
  if (al.ok && al.showSite) { // 基地模型的牆（「基地模型」關掉時不當遮擋物）
    for (const w of siteWalls()) {
      const a = siteToAR(w[0], w[1]), b = siteToAR(w[2], w[3]);
      if (distToSeg(tx, tz, a[0], a[1], b[0], b[1]) < 0.6) continue;
      const t = segT(ox, oz, tx, tz, a[0], a[1], b[0], b[1]);
      if (t !== null) occl(t, SITE_H);
    }
  }
  for (const o of omem) {
    if (o.hits < 2) continue;
    const bw = Math.max(0.15, Math.min(o.w, o.kb.w * 1.6));
    if (Math.hypot(tx - o.x, tz - o.z) < bw * 0.8) continue; // 目標就是這個物體
    const t = segBoxEntry(ox, oz, tx, tz, { x: o.x, z: o.z, w: bw, d: bw, rot: 0 }, 0);
    if (t !== null) occl(t, o.kb.h);
  }
  return hv;
}

// ---------- 編號與同步 ----------
function mkLocalId(m) {
  const cx = m.frame === 'site' ? m.sx : m.x, cz = m.frame === 'site' ? m.sz : m.z;
  let near = null, bd = 4.5;
  for (const q of mk.list) {
    if (!q.id || q.frame !== m.frame) continue;
    const qx = q.frame === 'site' ? q.sx : q.x, qz = q.frame === 'site' ? q.sz : q.z;
    const d = Math.hypot(qx - cx, qz - cz);
    if (d < bd) { bd = d; near = q; }
  }
  const letter = near ? near.id.split('-')[0] : String.fromCharCode(65 + (mk.localLetters.size % 26));
  const n = (mk.localLetters.get(letter) || 0) + 1;
  mk.localLetters.set(letter, n);
  return letter + '-' + n;
}

// site 座標 → AR 座標（每格重算，對位改變時自動跟著動）
function mkSync(m) {
  if (m.frame === 'site') {
    if (!al.ok) { m.vis = false; return; }
    const p = siteToAR(m.sx, m.sz);
    const n = mkRot(m.snx, m.snz, -al.phi);
    m.x = p[0]; m.z = p[1]; m.nx = n[0]; m.nz = n[1];
  }
  m.tx = -m.nz; m.tz = m.nx;
  m.vis = true;
}

function mkSend(m) {
  if (m.frame !== 'site' || m.sent || !net.on) return;
  m.sent = true;
  netSend({ t: 'mk', lid: m.lid, x: +m.sx.toFixed(2), z: +m.sz.toFixed(2), nx: +m.snx.toFixed(3), nz: +m.snz.toFixed(3), size: m.size, hm: m.hm, kind: m.kind });
}

function mkNetInit(list) { // 剛連上：收下房間裡已有的標記
  for (const q of list || []) mkNetAdd(q);
}
function mkNetAdd(q) {
  let m = mk.list.find((k) => k.id === q.id);
  if (!m && q.lid != null && q.by === net.id) m = mk.list.find((k) => k.lid === q.lid && k.src === 'local' && !k.id);
  if (m) { // 自己提出的：補上伺服器給的編號
    m.id = q.id; m.active = !!q.active || m.active;
    if (m.hitPending && !q.active) { netSend({ t: 'mkhit', id: m.id }); }
    m.hitPending = false;
    return;
  }
  mk.list.push({
    id: q.id, lid: 0, frame: 'site', src: 'net', sx: q.x, sz: q.z, snx: q.nx, snz: q.nz, size: q.size || MK_SIZE, hm: q.hm || 1.4, kind: q.kind || 'wall',
    by: q.by, active: !!q.active, actName: q.actName || '', sent: true, vis: false, born: performance.now(),
  });
}
function mkNetMap(m) { // 伺服器說「那裡已經有標記了」：丟掉自己的，不重複
  const k = mk.list.find((q) => q.lid === m.lid && q.src === 'local' && !q.id);
  if (!k) return;
  if (m.id == null) { k.dead = true; return; }
  const ex = mk.list.find((q) => q.id === m.id);
  if (ex) { k.dead = true; if (k.active && !ex.active) { netSend({ t: 'mkhit', id: ex.id }); ex.active = true; } }
  else k.id = m.id;
}
function mkNetAct(m) {
  const q = mk.list.find((k) => k.id === m.id);
  if (q) { q.active = true; q.actName = m.name; }
  if (m.by !== net.id) say(`${m.name} 啟用了標記 ${m.id}`, 2600);
}
function mkReset() { mk.list = []; mk.localLetters.clear(); mk.prog = 0; mk.cur = null; mk.fix = null; mk.created = 0; }
function mkDropLocalFrame() { // 校準：AR 座標系重來，只留 site 座標的標記
  mk.list = mk.list.filter((m) => m.frame === 'site');
  mk.prog = 0; mk.cur = null;
}

// ---------- 生成：挑牆面上「離 Canny 邊緣最遠」的平整處 ----------
function mkCandidates() {
  const out = [];
  const rej = mk.rej = { dist: 0, face: 0, cam: 0, scr: 0, occ: 0, edge: 0, near: 0, ok: 0 };
  const dt = mkDT();
  const fh = halfH();
  const eval1 = (P, n, tvec, size, kind, w) => {
    for (const hm of [1.1, 1.4, 1.7]) {
      const px = P[0] + n[0] * 0.012, pz = P[1] + n[1] * 0.012;
      const dx = px - pos.x, dz = pz - pos.z, dd = Math.hypot(dx, dz);
      if (dd < 1.0 || dd > 6.5) { rej.dist++; continue; }
      if (((pos.x - px) * n[0] + (pos.z - pz) * n[1]) / dd < 0.3) { rej.face++; continue; } // 要從正面看得到
      const c = toCam(dx, hm - EYE, dz);
      if (c[2] < 0.5) { rej.cam++; continue; }
      const sp = toScreen(c), rpx = (FPX * size * 0.5) / c[2];
      const mg = rpx + 8;
      if (sp[0] < mg || sp[0] > W - mg || sp[1] < mg || sp[1] > H - mg) { rej.scr++; continue; }
      if (visibleFloor(px + n[0] * 0.05, pz + n[1] * 0.05, w) >= hm - size / 2) { rej.occ++; continue; }
      const ci = Math.min(DW - 1, Math.max(0, Math.round(sp[0] / DS))), cj = Math.min(DH - 1, Math.max(0, Math.round(sp[1] / DS)));
      const clear = dt[cj * DW + ci] * DS; // 像素
      if (clear < rpx * 1.25 + 4) { rej.edge++; continue; } // 方塊範圍內（含四角）不能有邊緣
      let tooClose = false;
      for (const q of mk.list) {
        if (q.dead || !q.vis) continue;
        if (Math.hypot(q.x - px, q.z - pz) < 1.6) { tooClose = true; break; }
      }
      if (tooClose) { rej.near++; continue; }
      rej.ok++;
      const bearing = Math.abs(wrapPi(Math.atan2(dx, -dz) - gameHeading()));
      const score = Math.min(4, clear / rpx) - 0.9 * (bearing / fh) - 0.08 * dd - (hm === 1.4 ? 0 : 0.15);
      out.push({ x: px, z: pz, nx: n[0], nz: n[1], size, hm, kind, score, clear: clear / rpx });
    }
  };
  for (const w of world.walls) {
    if (w.hits < 4) continue;
    const s = sideOf(w);
    if (s.len < 0.9) continue;
    for (let a = 0.25; a <= s.len - 0.25; a += 0.25) {
      eval1([w.x1 + s.ux * a, w.z1 + s.uz * a], [s.nx, s.nz], [s.ux, s.uz], MK_SIZE, 'wall', w);
    }
  }
  for (const e of world.ents) {
    if (e.type !== 'column' || e.hits < 4 || e.w < 0.2) continue;
    const dx = pos.x - e.x, dz = pos.z - e.z, d = Math.hypot(dx, dz) || 1;
    const n = [dx / d, dz / d];
    eval1([e.x + n[0] * e.w / 2, e.z + n[1] * e.w / 2], n, [-n[1], n[0]], Math.min(MK_SIZE, e.w * 0.85), 'column', null);
  }
  return out;
}

function mkGen(now) {
  if (!running || now < mk.nextGen || !cannyFresh()) return;
  mk.nextGen = now + 2500;
  if (mk.list.filter((m) => !m.dead).length >= MK_MAX) return;
  if (angSpeed > 0.8) return; // 轉得太快、邊緣不穩時不挑
  const c = mkCandidates();
  if (!c.length) { mk.info = '找不到平整的牆面'; return; }
  c.sort((p, q) => q.score - p.score);
  const b = c[0];
  const m = {
    id: null, lid: mk.lid++, src: 'local', frame: al.ok ? 'site' : 'ar', x: b.x, z: b.z, nx: b.nx, nz: b.nz, size: b.size, hm: b.hm, kind: b.kind,
    by: net.id, active: false, sent: false, vis: true, born: now, clear: b.clear,
  };
  if (m.frame === 'site') {
    const p = arToSite(m.x, m.z), n = mkRot(m.nx, m.nz, al.phi);
    m.sx = p[0]; m.sz = p[1]; m.snx = n[0]; m.snz = n[1];
  }
  m.tx = -m.nz; m.tz = m.nx;
  mk.list.push(m);
  mk.created++;
  if (m.frame === 'site' && net.on) mkSend(m);
  else m.id = mkLocalId(m);
  mk.info = `新標記（離邊緣 ${b.clear.toFixed(1)}×）`;
}

// ---------- 掃描與啟用 ----------
function mkProject(m, dy, dl) { // 標記上的一點（沿牆切線 dl、鉛直 dy）→ 螢幕
  const c = toCam(m.x + m.tx * dl - pos.x, m.hm + dy - EYE, m.z + m.tz * dl - pos.z);
  return c[2] < 0.15 ? null : toScreen(c);
}

function mkScan(dt, now) {
  let best = null, bd = 1e9;
  for (const m of mk.list) {
    if (m.dead || !m.vis || m.active) continue;
    const dx = m.x - pos.x, dz = m.z - pos.z, d = Math.hypot(dx, dz);
    if (d > MK_ACT || d >= bd) continue;
    if (((pos.x - m.x) * m.nx + (pos.z - m.z) * m.nz) / (d || 1) < 0.25) continue;
    const c = toCam(dx, m.hm - EYE, dz);
    if (c[2] < 0.15) continue;
    const sp = toScreen(c);
    if (sp[0] < C.l || sp[0] > C.r || sp[1] < C.t || sp[1] > C.b) continue; // 只有中央清晰區的東西才「看得清楚」
    if (visibleFloor(m.x + m.nx * 0.05, m.z + m.nz * 0.05, null) >= m.hm - 0.1) continue;
    best = m; bd = d;
  }
  if (best && best === mk.cur) mk.prog = Math.min(1, mk.prog + dt / MK_HOLD);
  else if (best) { mk.cur = best; mk.prog = Math.min(mk.prog, 0.2) + dt / MK_HOLD; }
  else { mk.prog = Math.max(0, mk.prog - dt * 1.5); if (mk.prog <= 0) mk.cur = null; }
  if (mk.cur && mk.prog >= 1) { mkActivate(mk.cur, now); mk.prog = 0; mk.cur = null; }
}

function mkActivate(m, now) {
  m.active = true; m.actAt = now;
  try { if (navigator.vibrate) navigator.vibrate([30, 40, 30]); } catch (e) { /* ignore */ }
  say(`標記 ${m.id || '…'} 已啟用`, 2200);
  if (m.id) { if (net.on) netSend({ t: 'mkhit', id: m.id }); } else m.hitPending = true;
  if (m.src === 'net' || (m.by && m.by !== net.id)) mkFix(m);
}

// 位置修正：別人建立的標記（座標來自共用的 site 座標）貼在真牆上；
// 我自己偵測到的同一面牆若和它差了 δ，就代表我的位置推算漂移了 δ → 把位置挪回去一部分。
function mkFix(m) {
  let best = null, bd = 1.2;
  for (const w of world.walls) {
    if (w.hits < 3) continue;
    const len = Math.hypot(w.x2 - w.x1, w.z2 - w.z1) || 1;
    const wx = -(w.z2 - w.z1) / len, wz = (w.x2 - w.x1) / len; // 牆法向
    if (Math.abs(wx * m.nx + wz * m.nz) < 0.8) continue; // 要和標記同一個朝向
    const off = (m.x - w.x1) * wx + (m.z - w.z1) * wz;
    const t = ((m.x - w.x1) * (w.x2 - w.x1) + (m.z - w.z1) * (w.z2 - w.z1)) / (len * len);
    if (t < -0.15 || t > 1.15 || Math.abs(off) > bd) continue;
    bd = Math.abs(off); best = { off, wx, wz };
  }
  if (!best) { mk.fix = { txt: '無法修正（附近沒有偵測到同一面牆）', at: performance.now(), d: 0 }; return; }
  const d = Math.max(-1, Math.min(1, best.off)) * 0.6;
  pos.x += best.wx * d; pos.z += best.wz * d;
  mk.fix = { txt: `位置修正 ${(Math.abs(d) * 100).toFixed(0)} cm`, at: performance.now(), d };
  say(mk.fix.txt, 2000);
}

// ---------- 每格 ----------
let mkSig = '';
function mkTick(dt, now) {
  if (!running) return;
  // 對位改變 → 本機建立的標記重新換算 site 座標（它們貼在真牆上，真牆不動）
  const sig = al.ok ? `${al.A.x.toFixed(3)}|${al.phi.toFixed(4)}` : '';
  if (sig !== mkSig) {
    mkSig = sig;
    if (al.ok) {
      for (const m of mk.list) {
        if (m.src !== 'local' || m.frame !== 'ar' || m.dead) continue;
        const p = arToSite(m.x, m.z), n = mkRot(m.nx, m.nz, al.phi);
        m.frame = 'site'; m.sx = p[0]; m.sz = p[1]; m.snx = n[0]; m.snz = n[1]; m.sent = false; m.id = null; m.lid = mk.lid++;
      }
    }
  }
  mk.list = mk.list.filter((m) => !m.dead);
  for (const m of mk.list) {
    mkSync(m);
    if (m.frame === 'site' && m.src === 'local' && !m.sent && net.on) mkSend(m);
    if (m.frame === 'site' && m.src === 'local' && !m.sent && !net.on && !m.id) m.id = mkLocalId(m);
  }
  mkGen(now);
  mkScan(dt, now);
  if (net.on && al.ok && now - mk.lastWalls > 3000) { // 把偵測到的牆（site 座標）交給指揮端，地圖隨掃描擴張
    mk.lastWalls = now;
    const list = [];
    for (const w of world.walls) {
      if (w.hits < 4) continue;
      const a = arToSite(w.x1, w.z1), b = arToSite(w.x2, w.z2);
      list.push([a[0], a[1], b[0], b[1]]);
    }
    netSend({ t: 'walls', list: list.slice(0, 40) });
  }
}

// ---------- 畫面 ----------
function mkPattern(id, n) { // 由編號決定的 3×3 圖樣（純裝飾，讓標記看起來像一張貼紙）
  let h = 7;
  for (const ch of String(id || '?')) h = (h * 31 + ch.charCodeAt(0)) >>> 0;
  const cells = [];
  for (let i = 0; i < n * n; i++) { h = (Math.imul(h ^ (h >>> 15), 2246822519) + 374761393) >>> 0; cells.push((h >>> 7) & 1); }
  return cells;
}

function mkDrawOverlay(now) {
  ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  ctx.lineJoin = 'round';
  for (const m of mk.list) {
    if (m.dead || !m.vis) continue;
    const d = Math.hypot(m.x - pos.x, m.z - pos.z);
    if (d > MK_SEE) continue; // 太遠：偵測不到
    if (((pos.x - m.x) * m.nx + (pos.z - m.z) * m.nz) <= 0) continue; // 在牆的背面
    if (visibleFloor(m.x + m.nx * 0.05, m.z + m.nz * 0.05, null) >= m.hm - 0.1) continue;
    const h = m.size / 2;
    const q = [mkProject(m, h, -h), mkProject(m, h, h), mkProject(m, -h, h), mkProject(m, -h, -h)];
    if (q.some((p) => !p)) continue;
    const near = d <= MK_ACT;
    const col = m.active ? '110,255,225' : '255,255,255';
    ctx.strokeStyle = `rgba(${col},${near ? 0.95 : 0.35})`;
    ctx.lineWidth = near ? 2 : 1;
    ctx.beginPath(); ctx.moveTo(q[0][0], q[0][1]); for (let i = 1; i < 4; i++) ctx.lineTo(q[i][0], q[i][1]); ctx.closePath();
    if (m.active) { ctx.fillStyle = 'rgba(110,255,225,0.16)'; ctx.fill(); }
    ctx.stroke();
    if (!near) continue;
    // 3×3 圖樣
    const cells = mkPattern(m.id, 3);
    ctx.fillStyle = `rgba(${col},0.75)`;
    for (let i = 0; i < 9; i++) {
      if (!cells[i]) continue;
      const u0 = -h + (i % 3) * (m.size / 3) + m.size * 0.07, v0 = h - Math.floor(i / 3) * (m.size / 3) - m.size * 0.07, s = m.size / 3 - m.size * 0.14;
      const c4 = [mkProject(m, v0, u0), mkProject(m, v0, u0 + s), mkProject(m, v0 - s, u0 + s), mkProject(m, v0 - s, u0)];
      if (c4.some((p) => !p)) continue;
      ctx.beginPath(); ctx.moveTo(c4[0][0], c4[0][1]); for (let k = 1; k < 4; k++) ctx.lineTo(c4[k][0], c4[k][1]); ctx.closePath(); ctx.fill();
    }
    // 編號
    const cx0 = (q[0][0] + q[1][0] + q[2][0] + q[3][0]) / 4, cy1 = Math.max(q[2][1], q[3][1]) + 4;
    ctx.font = '600 13px ui-monospace, Menlo, monospace'; ctx.textAlign = 'center'; ctx.textBaseline = 'top';
    const t = (m.id || 'A-?') + (m.active ? ' ✓' : '');
    const tw = ctx.measureText(t).width + 10;
    ctx.fillStyle = 'rgba(0,0,0,0.6)'; ctx.fillRect(cx0 - tw / 2, cy1, tw, 18);
    ctx.fillStyle = m.active ? 'rgba(110,255,225,1)' : '#fff'; ctx.fillText(t, cx0, cy1 + 2);
    // 掃描進度環
    if (mk.cur === m && mk.prog > 0) {
      const cy0 = (q[0][1] + q[2][1]) / 2, r = Math.max(14, Math.hypot(q[0][0] - q[2][0], q[0][1] - q[2][1]) * 0.75);
      ctx.strokeStyle = 'rgba(110,255,225,0.95)'; ctx.lineWidth = 3;
      ctx.beginPath(); ctx.arc(cx0, cy0, r, -Math.PI / 2, -Math.PI / 2 + mk.prog * Math.PI * 2); ctx.stroke();
    }
  }
}

function mkRadar(put) {
  for (const m of mk.list) {
    if (m.dead || !m.vis) continue;
    put(m.x, m.z, m.active ? 'rgba(110,255,225,0.95)' : 'rgba(255,170,80,0.95)', 2.2);
  }
}

function mkHudLine() {
  const alive = mk.list.filter((m) => !m.dead);
  const act = alive.filter((m) => m.active).length;
  let near = null, bd = 1e9;
  for (const m of alive) {
    if (!m.vis || m.active) continue;
    const d = Math.hypot(m.x - pos.x, m.z - pos.z);
    if (d < bd) { bd = d; near = m; }
  }
  let t = `> 標記 ${act}/${alive.length} 已啟用`;
  if (near) t += `　最近 ${near.id || '…'} ${bd.toFixed(1)}m ${bd <= MK_ACT ? '（掃描中）' : '（走近到 ' + MK_ACT + 'm 內）'}`;
  if (!al.ok && !alive.length) t += '　（未對位：標記只存在本機）';
  return t;
}

function mkActiveNear(x, z, r) { // 地圖擴張：虛擬建築優先長在已啟用的標記附近
  for (const m of mk.list) if (m.active && m.vis && Math.hypot(m.x - x, m.z - z) < r) return true;
  return false;
}

// ==========================================================
// 人物偵測：鏡頭裡的人＝其他玩家＝敵人
//   模型：COCO-SSD（與物體辨識共用同一個模型，一次推論同時給出 person 與 cell phone）
//   規則：
//     · 拿著手機的人（手機框落在人框內）→ 連機玩家 → 敵人
//     · 位置和伺服器回報的某位玩家吻合（1.6 m 內）→ 那位玩家 → 敵人（並顯示名字）
//     · 伺服器上的其他玩家即使鏡頭沒拍到（例如在轉角後）也會依座標標示，但被擋住就不顯示
//     · 其餘的人 → 一般人，只畫淡的虛線框
//   敵人用白色實線框標記。被建築擋住就不顯示——虛擬生成的建築、偵測到的真實牆、基地模型的牆、
//   辨識到的大型物體都算；被矮的東西（掩體、桌椅）擋住時，只框出露在上方的那一部分。
//   距離：框底落在地面 → 眼高與俯仰角；腳被畫面切掉時改用「人高 1.7 m ÷ 框高」估距。
//   限制：COCO-SSD 在逆光、遠距（>8 m）、半身入鏡時會漏偵測；手機被手遮住就不算拿手機。
// ==========================================================
const PP_H = 1.75, PP_W = 0.55;
const pp = { tracks: [], nid: 1, items: [], hits: 0, lastN: 0 };

// preds：COCO-SSD 輸出；snap：送出辨識當下的姿態
function ppIngest(preds, snap) {
  const now = performance.now();
  const s = Math.max(snap.W / snap.vw, snap.H / snap.vh);
  const ox = (snap.W - snap.vw * s) / 2, oy = (snap.H - snap.vh * s) / 2;
  const persons = [], phones = [];
  for (const p of preds) {
    const b = { x: ox + p.bbox[0] * s, y: oy + p.bbox[1] * s, w: p.bbox[2] * s, h: p.bbox[3] * s, score: p.score };
    if (p.class === 'person' && p.score >= 0.45) persons.push(b);
    else if (p.class === 'cell phone' && p.score >= 0.25) phones.push(b);
  }
  pp.lastN = persons.length;
  for (const b of persons) {
    const cx = b.x + b.w / 2;
    const phone = phones.some((ph) => {
      const px = ph.x + ph.w / 2, py = ph.y + ph.h / 2;
      return px > b.x - b.w * 0.1 && px < b.x + b.w * 1.1 && py > b.y - b.h * 0.05 && py < b.y + b.h * 1.05;
    });
    const fp = withPose(snap, () => {
      if (b.y + b.h < snap.H - 8) {
        const f = floorPoint(cx, b.y + b.h);
        if (f && f.d > 0.6 && f.d < 14) return { x: f.x, z: f.z, d: f.d };
      }
      const r = rayW(cx, b.y + b.h * 0.5), l = Math.hypot(r[0], r[2]);
      if (l < 1e-3) return null;
      const d = Math.min(14, Math.max(0.8, (1.7 * snap.fpx) / Math.max(20, b.h)));
      return { x: pos.x + (r[0] / l) * d, z: pos.z + (r[2] / l) * d, d };
    });
    if (!fp) continue;
    // 和既有追蹤配對（1.2 m 內），沒有就新增
    let best = null, bd = 1.2;
    for (const t of pp.tracks) {
      const d = Math.hypot(t.x - fp.x, t.z - fp.z);
      if (d < bd) { bd = d; best = t; }
    }
    if (!best) { best = { id: pp.nid++, x: fp.x, z: fp.z, born: now, hits: 0, phoneAt: 0, peer: null }; pp.tracks.push(best); }
    else { best.x += (fp.x - best.x) * 0.5; best.z += (fp.z - best.z) * 0.5; }
    best.hits++; best.last = now; best.score = b.score; best.d = fp.d;
    if (phone) best.phoneAt = now;
  }
  pp.hits++;
}

// 注入已知的人（測試用，或日後接上其他偵測來源）
function ppInject(list) {
  const now = performance.now();
  for (const q of list) {
    let best = null;
    for (const t of pp.tracks) if (Math.hypot(t.x - q.x, t.z - q.z) < 0.6) best = t;
    if (!best) { best = { id: pp.nid++, x: q.x, z: q.z, born: now, hits: 0, phoneAt: 0, peer: null }; pp.tracks.push(best); }
    best.x = q.x; best.z = q.z; best.hits += 3; best.last = now; best.score = 0.9; best.d = Math.hypot(q.x - pos.x, q.z - pos.z);
    if (q.phone) best.phoneAt = now;
  }
}

function ppTick(dt, now) {
  pp.tracks = pp.tracks.filter((t) => now - t.last < 3000);
  const peers = netPeers();
  for (const t of pp.tracks) {
    t.peer = null;
    for (const p of peers) if (Math.hypot(p.x - t.x, p.z - t.z) < 1.6) { t.peer = p.o; break; }
    t.phone = now - t.phoneAt < 2500;
  }
  // 這一格要畫的清單
  const items = [];
  for (const t of pp.tracks) {
    if (now - t.last > 1200 || t.hits < 2) continue;
    items.push({ x: t.x, z: t.z, enemy: !!(t.phone || t.peer), name: t.peer ? t.peer.name : '', color: t.peer ? t.peer.color : '#fff', phone: t.phone, src: 'cam' });
  }
  for (const p of peers) { // 伺服器上的玩家：鏡頭沒配對到的也標示
    if (pp.tracks.some((t) => t.peer === p.o && now - t.last < 1200 && t.hits >= 2)) continue;
    if (p.d < 0.4 || p.d > 25) continue;
    items.push({ x: p.x, z: p.z, enemy: true, name: p.o.name, color: p.o.color, phone: false, src: 'net' });
  }
  for (const it of items) {
    it.d = Math.hypot(it.x - pos.x, it.z - pos.z);
    it.hv = visibleFloor(it.x, it.z, null); // 目標處可見的最低高度
  }
  pp.items = items;
}

function ppBox(it, hv) {
  // 人形外框（寬 0.55、高 1.75）八個角投影成螢幕矩形；底邊抬到「可見的最低高度」
  const dx = it.x - pos.x, dz = it.z - pos.z, d = Math.hypot(dx, dz) || 1;
  const rx = -dz / d * PP_W / 2, rz = dx / d * PP_W / 2;
  let x0 = 1e9, x1 = -1e9, y0 = 1e9, y1 = -1e9;
  for (const y of [Math.max(0, hv), PP_H]) {
    for (const sg of [-1, 1]) {
      const c = toCam(dx + rx * sg, y - EYE, dz + rz * sg);
      if (c[2] < 0.3) return null;
      const p = toScreen(c);
      x0 = Math.min(x0, p[0]); x1 = Math.max(x1, p[0]); y0 = Math.min(y0, p[1]); y1 = Math.max(y1, p[1]);
    }
  }
  if (x1 < 0 || x0 > W || y1 < 0 || y0 > H) return null;
  return { x: x0, y: y0, w: x1 - x0, h: y1 - y0 };
}

function ppDrawOverlay(now) {
  if (!running) return;
  ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  ctx.font = '600 12px -apple-system, "PingFang TC", sans-serif';
  ctx.textAlign = 'left'; ctx.textBaseline = 'bottom';
  pp.drawn = 0;
  for (const it of pp.items) {
    if (it.hv >= PP_H - 0.15) continue; // 被擋住：不顯示
    const b = ppBox(it, it.hv);
    if (!b || b.h < 8) continue;
    pp.drawn++;
    const lab = it.enemy
      ? `敵人${it.name ? '・' + it.name : ''}${it.phone && !it.name ? '・持手機' : ''}　${it.d.toFixed(1)}m`
      : `人　${it.d.toFixed(1)}m`;
    if (it.enemy) {
      ctx.strokeStyle = '#fff'; ctx.lineWidth = 2; ctx.setLineDash([]);
      ctx.strokeRect(b.x, b.y, b.w, b.h);
      const k = Math.min(14, b.w * 0.3, b.h * 0.3); // 四角加粗，像鎖定框
      ctx.lineWidth = 4; ctx.beginPath();
      for (const [cx0, cy0, sx, sy] of [[b.x, b.y, 1, 1], [b.x + b.w, b.y, -1, 1], [b.x, b.y + b.h, 1, -1], [b.x + b.w, b.y + b.h, -1, -1]]) {
        ctx.moveTo(cx0 + sx * k, cy0); ctx.lineTo(cx0, cy0); ctx.lineTo(cx0, cy0 + sy * k);
      }
      ctx.stroke();
    } else {
      ctx.strokeStyle = 'rgba(255,255,255,0.45)'; ctx.lineWidth = 1; ctx.setLineDash([6, 5]);
      ctx.strokeRect(b.x, b.y, b.w, b.h); ctx.setLineDash([]);
    }
    const tw = ctx.measureText(lab).width + 10, ly = Math.max(18, b.y);
    ctx.fillStyle = 'rgba(0,0,0,0.6)'; ctx.fillRect(b.x, ly - 17, tw, 17);
    ctx.fillStyle = it.enemy ? '#fff' : 'rgba(255,255,255,0.7)'; ctx.fillText(lab, b.x + 5, ly - 3);
  }
}

function ppHudLine() {
  const en = pp.items.filter((i) => i.enemy);
  const vis = en.filter((i) => i.hv < PP_H - 0.15).length;
  return `> 人物：${S.people ? (ob.ready ? '偵測中' : ob.status) : '關閉'}　敵人 ${vis}/${en.length}（看得到/總數）`;
}

function ppRadar(put) {
  for (const it of pp.items) if (it.enemy) put(it.x, it.z, '#fff', 2.8);
}

// ==========================================================
// 移動
// ==========================================================
function updateMove(dt) {
  if (holdWalk) pending = Math.min(pending + 1.3 * dt, 2);
  const mv = Math.min(pending, 2.0 * dt);
  pending -= mv;
  pos.x += headX * mv;
  pos.z += headZ * mv;
  moveSpeed += (mv / Math.max(dt, 1e-3) - moveSpeed) * Math.min(1, dt * 6);
  if (moveSpeed < 0.02) moveSpeed = 0;
}

let accBase = 9.8, prevSig = 0, lastStep = 0;
function onMotion(e) {
  const rr = e.rotationRate;
  if (rr && rr.alpha != null) cmp.gyro += (Math.hypot(rr.alpha, rr.beta, rr.gamma) - cmp.gyro) * 0.2;
  const a = e.accelerationIncludingGravity;
  if (!a || a.x == null) return;
  const mag = Math.hypot(a.x, a.y, a.z);
  accBase += (mag - accBase) * 0.08;
  const sig = mag - accBase;
  const now = performance.now();
  if (sig > 1.3 && prevSig <= 1.3 && now - lastStep > 320) {
    lastStep = now;
    steps++;
    pending += S.stepLen;
  }
  prevSig = sig;
}

function onOrient(e) {
  if (e.beta == null || e.gamma == null) return;
  sensor.a = e.alpha == null ? 0 : e.alpha;
  sensor.b = e.beta;
  sensor.g = e.gamma;
  sensor.seen = true;
  hasSensor = true;
  cmpFromEvent(e);
}

// ==========================================================
// 文字（畫在主畫布上）
// ==========================================================
function pct(v) { return Math.round(v * 100) + '%'; }

function drawHud(now) {
  ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  if (!S.showHud) {
    if (now < genLog.until) hudBox([`> ${genLog.text}`]);
    return;
  }
  const wc = worldCounts();
  const lines = [
    `> 視野 左${pct(fov.l)} 右${pct(fov.r)} 上下${pct(fov.u)}　${moveSpeed.toFixed(1)} m/s`,
    `> 空間 柱${wc.col} 角${wc.cor} 牆${wc.wall} 邊${wc.edg}　地板${pct(det.floorPct)}　${det.ms.toFixed(0)}ms`,
    `> 習慣 空曠${pct(habit.open)} 貼牆${pct(habit.hug)} 快走${pct(habit.fast)} 停留${pct(habit.still)}`,
    `> 建築 ${new Set(obs.filter((o) => o.gen && !o.dying).map((o) => o.gid)).size} 處　步數 ${steps}　亂度 ${pct(susp.erratic)}`,
  ];
  if (ob.on || ob.status.startsWith('載入失敗')) lines.push(`> 物體：${omem.filter((o) => o.hits >= 2).length} 個　${ob.status}`);
  if (!wc.col && !wc.cor && !wc.wall && !S.freeGen) lines.push('> 掃描空間中…請緩慢環視牆角、柱子與地面');
  else if (now < genLog.until) lines.push(`> ${genLog.text}`);
  if (!hasSensor) lines.push('> 無方向感測：拖曳轉向');
  const nl = netHudLine();
  if (nl) lines.push(nl);
  lines.push(mkHudLine());
  lines.push(ppHudLine());
  lines.push(`> 深度：${det.depth}`);
  hudBox(lines);
}

function hudBox(lines) {
  const top = 10 + SAFE_TOP;
  ctx.font = '11px ui-monospace, Menlo, monospace';
  const maxW = Math.max(120, W - 16 - 110);
  const fit = (t) => { while (t.length > 2 && ctx.measureText(t).width > maxW - 16) t = t.slice(0, -2) + '…'; return t; };
  lines = lines.map(fit);
  let w = 0;
  for (const t of lines) w = Math.max(w, ctx.measureText(t).width);
  ctx.fillStyle = 'rgba(0,0,0,0.55)';
  ctx.fillRect(8, top - 4, w + 16, lines.length * 15 + 8);
  ctx.fillStyle = 'rgba(255,255,255,0.92)';
  ctx.textAlign = 'left';
  ctx.textBaseline = 'top';
  lines.forEach((t, i) => ctx.fillText(t, 16, top + i * 15));
}

// ==========================================================
// 主迴圈
// ==========================================================
function frame(t) {
  requestAnimationFrame(frame);
  if (!running) return;
  const dt = Math.min(0.1, Math.max(0.001, (t - lastT) / 1000));
  lastT = t;
  timeSinceStart += dt;

  const now = performance.now();
  updateCamera();
  trackAng(dt);
  updateMove(dt);
  updateVision();
  updateHabit(dt);
  updateSuspense(dt, now);
  updateCompass();
  updateAlign();
  netTick(dt, now);
  mkTick(dt, now);
  ppTick(dt, now);
  scUpdate(now);
  updateGeneration(now);

  drawVideo();
  if (++detTick % 4 === 0) runDetection(now);
  runObjects(now); // 在畫上虛擬物之前，只分析真實影像
  if (S.showDet) drawWorld(sctx);
  if (S.showDet) drawObjects(sctx);
  drawSite(sctx, now);
  drawNet(sctx, now);
  drawStructures(sctx);
  drawSuspScene(sctx, now);
  if (S.limitOn) {
    composeLimited();
  } else {
    ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
    ctx.drawImage(scene, 0, 0, W, H);
    C = centerRect();
  }
  if (S.showDet) drawDetOverlay();
  drawSuspOverlay(now);
  drawCompass();
  drawAlignOverlay();
  drawObjOverlay(now);
  drawNetOverlay();
  mkDrawOverlay(now);
  ppDrawOverlay(now);
  drawHud(performance.now());
}

// ==========================================================
// 啟動與操作
// ==========================================================
function calibrate() {
  // 把目前手機朝向當作「前方」；座標系改變，世界模型也要重建
  h0 = null;
  yawM = 0;
  world.ents = []; world.walls = []; world.free.clear();
  clearObjects();
  obs = obs.filter((o) => !o.gen);
  cmp.have = false;
  alignReset();
  scReset();
  mkDropLocalFrame();
  pp.tracks = [];
}

function resetWorld() {
  obs = [];
  pos.x = pos.z = 0;
  pending = 0;
  moveSpeed = 0;
  steps = 0;
  resetHabit();
  world.ents = []; world.walls = []; world.free.clear();
  resetSuspense();
  alignReset();
  clearObjects();
  scReset();
  mkReset();
  pp.tracks = [];
}

function seedWorld() {
  updateCamera();
  nextGenAt = performance.now() + GEN_FIRST;
}

async function start() {
  const err = $('err');
  err.textContent = '';
  try {
    // iOS 需要在點擊當下要求動作與方向感測的權限
    if (typeof DeviceOrientationEvent !== 'undefined' && typeof DeviceOrientationEvent.requestPermission === 'function') {
      const r = await DeviceOrientationEvent.requestPermission();
      if (r !== 'granted') err.textContent = '沒有取得方向感測權限，將改用拖曳螢幕轉向。';
    }
    if (typeof DeviceMotionEvent !== 'undefined' && typeof DeviceMotionEvent.requestPermission === 'function') {
      try { await DeviceMotionEvent.requestPermission(); } catch (e) { /* 沒有也能用「按住前進」 */ }
    }
  } catch (e) {
    err.textContent = '感測器權限被拒絕，將改用拖曳螢幕轉向。';
  }

  audioInit();
  probeDepth();
  window.addEventListener('deviceorientation', onOrient);
  window.addEventListener('deviceorientationabsolute', onOrientAbs);
  window.addEventListener('devicemotion', onMotion);

  try {
    if (!navigator.mediaDevices || !navigator.mediaDevices.getUserMedia) throw new Error('此瀏覽器不支援鏡頭（需要 https 網址）');
    const stream = await navigator.mediaDevices.getUserMedia({
      video: { facingMode: { ideal: 'environment' }, width: { ideal: 1280 }, height: { ideal: 720 } },
      audio: false,
    });
    video.srcObject = stream;
    await video.play();
  } catch (e) {
    err.textContent = '無法開啟鏡頭：' + (e && e.message ? e.message : e) + '。可以先用深色背景測試，但看不到真實空間。';
    await new Promise((res) => setTimeout(res, 1800));
  }

  try { if (navigator.wakeLock) await navigator.wakeLock.request('screen'); } catch (e) { /* ignore */ }

  $('intro').style.display = 'none';
  $('bar').hidden = false;
  resize();
  resetWorld();
  calibrate();
  seedWorld();
  running = true;
  if (net.autoConnect) { net.autoConnect = false; netConnect(); }
  if (S.people) ensureModel();
  lastT = performance.now();
}

function bindUI() {
  $('start').addEventListener('click', start);
  $('bCal').addEventListener('click', calibrate);
  $('bLimit').addEventListener('click', (e) => {
    S.limitOn = !S.limitOn;
    e.currentTarget.classList.toggle('on', S.limitOn);
  });
  const walk = $('bWalk');
  const on = (e) => { e.preventDefault(); holdWalk = true; walk.classList.add('on'); };
  const off = (e) => { e.preventDefault(); holdWalk = false; walk.classList.remove('on'); };
  walk.addEventListener('pointerdown', on);
  walk.addEventListener('pointerup', off);
  walk.addEventListener('pointercancel', off);
  walk.addEventListener('pointerleave', off);
  $('bSet').addEventListener('click', () => $('panel').classList.toggle('open'));

  const bind = (id, out, key, fmt, onChange) => {
    const el = $(id), o = $(out);
    el.value = S[key];
    o.textContent = fmt(S[key]);
    el.addEventListener('input', () => {
      S[key] = parseFloat(el.value);
      o.textContent = fmt(S[key]);
      if (onChange) onChange();
      saveSettings();
    });
  };
  bind('sSize', 'oSize', 'sizeMul', (v) => v.toFixed(2), () => { C = centerRect(); });
  bind('sFov', 'oFov', 'fovLong', (v) => v + '°');
  bind('sStep', 'oStep', 'stepLen', (v) => v.toFixed(2));
  bind('sDot', 'oDot', 'dotThreshold', (v) => String(v));
  const hudBtn = $('bHud');
  hudBtn.classList.toggle('on', S.showHud);
  hudBtn.addEventListener('click', () => { S.showHud = !S.showHud; hudBtn.classList.toggle('on', S.showHud); saveSettings(); });
  $('bClear').addEventListener('click', () => { obs = obs.filter((o) => !o.gen); genCount = 0; genHistory = []; });
  let dbg = false;
  try { dbg = new URLSearchParams(location.search).get('debug') === '1'; } catch (e) { /* ignore */ }
  if (dbg) { S.showDet = true; S.showCanny = true; document.querySelectorAll('.dev').forEach((e) => { e.hidden = false; }); }
  const ppBtn = $('bPeople');
  ppBtn.classList.toggle('on', S.people);
  ppBtn.addEventListener('click', () => { S.people = !S.people; ppBtn.classList.toggle('on', S.people); saveSettings(); if (S.people) ensureModel(); });
  $('bMkClear').addEventListener('click', () => { mkReset(); });
  const cnBtn = $('bCanny');
  cnBtn.classList.toggle('on', S.cannyOn);
  cnBtn.addEventListener('click', () => { S.cannyOn = !S.cannyOn; cnBtn.classList.toggle('on', S.cannyOn); saveSettings(); });
  const cnvBtn = $('bCannyView');
  cnvBtn.classList.toggle('on', S.showCanny);
  cnvBtn.addEventListener('click', () => { S.showCanny = !S.showCanny; cnvBtn.classList.toggle('on', S.showCanny); saveSettings(); });
  const detBtn = $('bDet');
  detBtn.classList.toggle('on', S.showDet);
  detBtn.addEventListener('click', () => { S.showDet = !S.showDet; detBtn.classList.toggle('on', S.showDet); saveSettings(); });
  const freeBtn = $('bFree');
  freeBtn.classList.toggle('on', S.freeGen);
  freeBtn.addEventListener('click', () => { S.freeGen = !S.freeGen; freeBtn.classList.toggle('on', S.freeGen); });
  $('bAlign').addEventListener('click', alignConfirm);
  const objBtn = $('bObj');
  objBtn.addEventListener('click', async () => { await toggleObjects(); objBtn.classList.toggle('on', ob.on); });
  cv.addEventListener('click', (e) => { tapObjects(e.clientX, e.clientY); });
  $('bSite').addEventListener('click', (e) => { al.showSite = !al.showSite; e.currentTarget.classList.toggle('on', al.showSite); });
  $('bScale').addEventListener('click', applyScale);
  const sl = $('sSiteL'), ol = $('oSiteL');
  sl.value = al.L; ol.textContent = al.L.toFixed(1);
  sl.addEventListener('input', () => { al.L = parseFloat(sl.value); ol.textContent = al.L.toFixed(1); alignReset(); });
  $('bSus').addEventListener('click', () => { audioInit(); triggerSuspense(); });
  $('bScan').addEventListener('click', () => { world.ents = []; world.walls = []; world.free.clear(); });
  $('bGen').addEventListener('click', () => { generateByHabit(); });

  // 沒有方向感測器時（桌機測試）：拖曳轉向、WASD 前進
  let drag = null;
  cv.addEventListener('pointerdown', (e) => { drag = { x: e.clientX, y: e.clientY }; });
  window.addEventListener('pointerup', () => { drag = null; });
  window.addEventListener('pointermove', (e) => {
    if (!drag || (hasSensor && sensor.seen)) return;
    yawM += (e.clientX - drag.x) * 0.006;
    pitchM = Math.max(-1.3, Math.min(1.3, pitchM - (e.clientY - drag.y) * 0.006));
    drag = { x: e.clientX, y: e.clientY };
  });
  window.addEventListener('keydown', (e) => { if (e.code === 'KeyW') holdWalk = true; });
  window.addEventListener('keyup', (e) => { if (e.code === 'KeyW') holdWalk = false; });
}

loadSettings();
bindUI();
netInit();
resize();
requestAnimationFrame(frame);

// 供除錯與自動測試使用
window.__ar = { mk, pp, sc, ppInject, mkCandidates, mkDT, visibleFloor, mkActivate, mkTick, ppTick, ppIngest, scMul, scBin, net, netConnect, netDisconnect, netSetState, netEvent, netPeers, cn, get cmask() { return cmask; }, ob, omem, OKB, processDetections, tapObjects, toggleObjects, al, alR, arToSite, siteToAR, alignConfirm, applyScale, siteWalls, siteItems, hiddenByRealWall, S, fov, habit, get obs() { return obs; }, pos, sensor, tryPlace, generateByHabit, start, calibrate, world, det, cmp, susp, injectWorld, triggerSuspense, runDetection, worldCounts, get B() { return B; }, get FPX() { return FPX; }, get head() { return [headX, headZ]; } };
})();