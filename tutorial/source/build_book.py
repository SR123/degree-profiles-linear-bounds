from pathlib import Path
import json
p=Path(__file__).resolve().parent
orders=json.loads((p/'chapter_order.json').read_text())
names=['00_preface','00_reader']+[name for _,seq in orders for name in seq]
missing=[name for name in names if not (p/'chapters'/f'{name}.tex').exists()]
if missing:raise SystemExit('Awaiting chapters: '+', '.join(missing))
parts=[(p/'preamble.tex').read_text(),(p/'chapters/00_preface.tex').read_text(),(p/'chapters/00_reader.tex').read_text()]
for title,seq in orders:
 parts.append('\\part{'+title+'}\n')
 parts.extend((p/'chapters'/f'{name}.tex').read_text() for name in seq)
parts.append((p/'references.tex').read_text())
parts.append('\\end{document}\n')
(p/'main.tex').write_text('\n'.join(parts))
print('Assembled complete book:',len((p/'main.tex').read_text().split()),'source words')
