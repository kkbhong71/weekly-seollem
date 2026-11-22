# 빌드: page.html + engine_v2.js + 최신 ../../data/new_XXXX.csv → ../index.html
# 실행: precision/src 폴더에서  python3 build.py
# 원리: 당첨번호를 '알파벳 1글자 = 번호 1개'로 압축해 HTML 안에 내장 → 인터넷이 끊겨도 동작.
#       화면에서는 실행할 때마다 ../data/new_XXXX.csv를 다시 찾아 최신 회차를 더함(매주 빌드 불필요).
import csv, glob, os, re
os.chdir(os.path.dirname(os.path.abspath(__file__)))
A = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrs'
files = sorted(glob.glob('../../data/new_*.csv'), key=lambda f: int(re.findall(r'new_(\d+)', f)[0]))
src = files[-1]
rows = sorted(csv.DictReader(open(src, encoding='utf-8-sig')), key=lambda r: int(r['round']))
assert [int(r['round']) for r in rows] == list(range(1, len(rows) + 1)), '회차가 1부터 빠짐없이 이어져야 합니다'
data = ''.join(''.join(A[int(r[f'num{i}']) - 1] for i in range(1, 7)) for r in rows)
page, eng = open('page.html', encoding='utf-8').read(), open('engine_v2.js', encoding='utf-8').read()
out = page.replace('/*__ENGINE__*/', eng).replace("'__DATA__'", "'" + data + "'")
open('../index.html', 'w', encoding='utf-8').write(out)
print('built ../index.html', len(out), 'bytes · data from', src, '· rounds', len(rows))
