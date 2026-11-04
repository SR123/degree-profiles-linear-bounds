Author-review editorial revision, 4 November 2026.

Compile the standalone main.tex with pdflatex/latexmk. Organised sources
are in sections/; after editing run python3 build_paper.py, then compile main.tex.
The exported paper has 78 pages. The abstract credits the LICS 2008/2009
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
PDF SHA256: 697ca04c2b07a34f7e26a17d35e858725b1243eb6df75f6b8287ef35f6cc8894

Section 2.4 fixed-degree qualification, 4 November 2026: the Boolean upper
bound d_PC <= d_NS <= v+D is retained. Razborov's Omega(v) PC lower bound
for modified pigeonhole encodings is cited only for comparison, allowing
logarithmic input degree. The paragraph explicitly says this does not
establish sharpness in our uniform class, which fixes D independently of n.
Only the literature paragraph changed in this revision. Theorems and proofs
are unchanged. The packet matches the current 78-page paper.

Proof-source archive links, 4 November 2026: the final verification
paragraph now cites the supporting-materials bibliography entry [30].
That entry links to a fixed GitHub repository archive, its archived paper
PDF, and the Lean sources and verification records, all at commit
072d949368e3ad7f44fc3b34b80d8f43fa92dcd1. The local ZIP filename was
removed from the paragraph. The acknowledgements are unchanged.
The paper remains 78 pages; the PDF hyperlink destinations were checked.
This task updates local paper artifacts; it does not upload a GitHub revision.
