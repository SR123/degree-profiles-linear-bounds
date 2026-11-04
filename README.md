# Degree profiles of uniform polynomial consequences

**Author-review draft — tutorial updated 5 November 2026.**

Søren Riis, *Degree profiles of uniform polynomial consequences: Linear lower bounds for Nullstellensatz and Polynomial Calculus*.

- [Paper](paper/paper.pdf) — the 78-page manuscript with the author's requested editorial revision.
- [Tutorial](tutorial/tutorial.pdf) — the revised 193-page companion, *Understanding the linear degree gap*.
- [Lean formalisation and reproduction instructions](lean/README.md) — the preserved formal source packet, with its own scope and evidence records.
- [Tutorial review and verification scope](verification/REVIEW.txt).
- [Reference and connection checks](verification/REFERENCES.txt).

The latest paper revision is described in [the revision note](verification/PAPER-UPDATE.txt). It updates the abstract, notation, examples, historical attribution, and the discussion of Nullstellensatz completeness and degree upper bounds. The tutorial has now been aligned with this paper: see [the tutorial revision note](verification/TUTORIAL-UPDATE.txt). Target notation and degree terminology are consistent, Chapter 18 develops Section 11’s topological classification, and Euler structures are optional background rather than a characterisation of the four types. The Lean packet is unchanged.

## Citation

Søren Riis. *Degree profiles of uniform polynomial consequences: Linear lower bounds for Nullstellensatz and Polynomial Calculus*. Author-review draft, 4 November 2026.

This snapshot has no DOI. Bibliographic details are also provided in [CITATION.txt](CITATION.txt).

## Suggested reading

Start with “Reading alongside the current paper” in the tutorial's front matter (PDF pages 9–10). The table points from questions about the paper to the relevant tutorial chapters.

Chapter 18, especially §18.1 (PDF pages 165–167), explains the four types through a residue tree and the hardness spectrum. It includes a binary example, explains compactness, and separates the qualitative topological description from the quantitative estimates responsible for linear lower bounds. The spectrum is a reformulation of residue-class information already implicit in Riis's 2009 report; it is not claimed as a new classification.

Section 20.7 explains links to proof complexity, modular representation stability, exactness, rook operators, designs, and p-adic topology. It distinguishes proof ingredients from background analogies. The Euler-model criterion is not asserted to have a general converse.

## What has and has not been verified

The tutorial compiles, its finite worked-example checks pass, and its notation and reference uses have been compared with the current paper. These are not an independent reproof of every theorem in the paper or the textbook.

The Lean sources and recorded audit results are preserved unchanged. The packet's integrity/import checks and its checks of recorded audit outputs pass. **No fresh Lean build or kernel replay was performed during this tutorial review.** The new topological exposition has a written proof, not a new Lean endpoint. Other written-only claims and the exact existing formal scope are described in [lean/SCOPE.md](lean/SCOPE.md) and [lean/EVIDENCE.md](lean/EVIDENCE.md).

## Reproduce the documents

Python 3 and a LaTeX distribution with `latexmk` are needed. From `paper/source`:

```sh
python3 build_paper.py
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build main.tex
```

From `tutorial/source`:

```sh
python3 build_book.py
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build main.tex
```

Each produces `build/main.pdf`. PDF creation metadata may differ from the distributed copy. The paper PDF and source were rebuilt for the later editorial revision. The reviewed 193-page tutorial is retained unchanged.

## Check files and examples

At the package root, before making edits:

```sh
python3 verify_files.py
```

To repeat the finite illustration checks, use Python 3 on each `check_*.py` file in `tutorial/checks`. They write their corresponding JSON results beside the scripts. These finite checks illustrate calculations; they do not prove the general asymptotic claims. For actual Lean reconstruction, follow [lean/README.md](lean/README.md), including its pinned dependencies and distinction between builds, historical evidence, and fresh checker replay.

No release or DOI has been created. No new redistribution licence has been selected by this preparation step; the preserved Lean packet records the outstanding policy choices in [lean/RELEASE_POLICY.md](lean/RELEASE_POLICY.md). Author review remains outstanding.
