/* 일주일의 설렘 서비스 워커
   - 화면(index.html)·아이콘: '네트워크 먼저' → 새 버전이 올라오면 바로 반영, 인터넷이 끊기면 저장해 둔 화면으로 열림
   - 당첨번호 CSV: 항상 네트워크(오래된 데이터를 보여 주지 않기 위해), 실패 시에만 저장본
   - 외부(drand·USGS·폰트): 손대지 않음 */
const CACHE = 'seollem-v0.8';
const CORE = ['./', './index.html', './manifest.webmanifest', './icon-192.png', './icon-512.png'];
self.addEventListener('install', e => { e.waitUntil(caches.open(CACHE).then(c => c.addAll(CORE)).then(() => self.skipWaiting())); });
self.addEventListener('activate', e => {
  e.waitUntil(caches.keys().then(keys => Promise.all(keys.filter(k => k !== CACHE).map(k => caches.delete(k)))).then(() => self.clients.claim()));
});
self.addEventListener('fetch', e => {
  const url = new URL(e.request.url);
  if (e.request.method !== 'GET' || url.origin !== location.origin) return;
  e.respondWith(fetch(e.request).then(res => {
    if (res.ok) { const copy = res.clone(); caches.open(CACHE).then(c => c.put(e.request, copy)); }
    return res;
  }).catch(() => caches.match(e.request).then(r => r || caches.match('./index.html'))));
});
