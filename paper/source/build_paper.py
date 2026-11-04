from pathlib import Path
p=Path(__file__).resolve().parent
names=['introduction','systems','classification','transfer','block_algebra','quadratic','linear_layers','rooks','odd','comparison','model_theory','target_examples','examples','matching','undecidability','conclusion','references']
missing=[name for name in names if not (p/'sections'/f'{name}.tex').exists()]
if missing:raise SystemExit('Awaiting sections: '+', '.join(missing))
text=(p/'preamble.tex').read_text()+'\n'.join((p/'sections'/f'{name}.tex').read_text() for name in names)+'\n\\end{document}\n'
(p/'main.tex').write_text(text)
print('Assembled standalone main.tex:',len(text.split()),'source words')
