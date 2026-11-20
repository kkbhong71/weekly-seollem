# 빌드: src.html + engine.js + data.txt → ../index.html  (실행: src 폴더에서 python3 build.py)
# data.txt 갱신: ../data/에 최신 new_XXXX.csv를 넣은 뒤 python3 build.py --data
import sys, csv, os
os.chdir(os.path.dirname(os.path.abspath(__file__)))
if '--data' in sys.argv:
    A = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrs'
    import glob, re
    files = sorted(glob.glob('../data/new_*.csv'), key=lambda f: int(re.findall(r'new_(\d+)', f)[0]))
    print('data from', files[-1])
    rows = sorted(csv.DictReader(open(files[-1], encoding='utf-8-sig')), key=lambda r: int(r['round']))
    open('data.txt', 'w').write(''.join(''.join(A[int(r[f'num{i}']) - 1] for i in range(1, 7)) for r in rows))
src = open('src.html').read(); eng = open('engine.js').read(); data = open('data.txt').read()
out = src.replace('/*__ENGINE__*/', eng).replace("'__DATA__'", "'" + data + "'")
open('../index.html', 'w').write(out); print('built ../index.html', len(out), 'rounds', len(data) // 6)
