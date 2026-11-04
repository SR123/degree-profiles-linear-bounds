Version 1.0.0 — DOI archive, 5 November 2026.

Compile main.tex with pdflatex/latexmk. After editing the organised sections, run python3 build_paper.py before compiling.

The 78-page paper cites the combined paper and supporting-material archive in reference [30]: https://doi.org/10.5281/zenodo.23965838
The abstract points to this reference for the tutorial, Lean formalisation and verification records.

Licence: CC BY 4.0; upstream dependencies retain their own licences. The DOI preparation changes citation and packaging metadata, not mathematical statements or Lean proofs. No fresh Lean kernel replay was performed.

Section 11 gives the general p-adic hardness spectrum. Its topological exposition is written mathematics, not a new Lean endpoint. See lean/SCOPE.md and lean/EVIDENCE.md for formalisation scope.

The unused finite_certificate.tex is retained as supplied and is not part of build_paper.py assembly order.

PDF SHA256: 10ce41444b11132d389a2a77d99d85061caf67e5a2788b51ebf248aaafb20c60
