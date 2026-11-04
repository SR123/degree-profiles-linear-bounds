Author-review editorial revision, 4 November 2026.

Compile the standalone main.tex with pdflatex/latexmk. Organised sources
are in sections/; after editing run python3 build_paper.py, then compile main.tex.
The exported paper has 77 pages. The abstract credits the LICS 2008/2009
classification before the current linear bounds and uniform-target extension.
New introductory examples explain global sums, tuple-indexed variables, orbit
generators, permanently named parameters, zero-arity types and the first-order
compiler. Constants chosen by a model are distinguished from fixed parameters.
The theorem statements and proof bodies are unchanged.

Section 11.1 gives the general p-adic hardness spectrum and four shapes,
crediting the author's 2009 report, Section 4. This is written mathematics,
not a new Lean endpoint. The preserved degree-profiles-lean-source.zip
contains the core formal sources and exact scope/evidence. No fresh Lean
build or replay was performed for this editorial revision.
The separate finite_certificate.tex is retained as supplied and is not
part of build_paper.py's assembly order.

No publication or submission has occurred. Licence choices remain unchanged.
PDF SHA256: 6b986896daefd8cd4f328a3ae69391a4e9b3ed63b9750451a750ce397c244c14
