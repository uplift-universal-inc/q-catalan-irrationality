# Editorial and release preparation record

Date: 12 October 2026 (UTC). Canonical manuscript: `paper/main.tex`, with `introduction.tex` and `references.tex`. Style authority: the `latex-math-writing` house style supplied by the `math-paper-campaign` workflow, from `amelieloher/math-paper-skills` revision `e2f73a884ae32487d02dfd10ce8619121daf95d6`.

## Mathematical and manuscript disposition

The theorem and conservative constants were frozen before composition. Each load-bearing dependency has both an all-index written proof and a separately scoped internal review. The final fresh reader read the complete canonical TeX and found no blocker. Its exact input hashes match the release manuscript. The optional sharper denominator bound and mixed extension were not inserted into the main theorem.

The canonical editor made these substantive expository changes from the source:

1. Defined the derivative functional continuously on `C¹[0,q]`, with an explicit norm bound.
2. Included the exact local remainder as complete homogeneous polynomials, retaining the polynomial quotient.
3. Explained the formal nature of the two-variable interpolation at roots of unity and displayed the residue's square factor.
4. Supplied the elementary totient derivation and tail truncation for the cost.
5. Clarified the Cauchy transform's continued domain and local uniform convergence, and restricted geometric expansions to exterior regions.
6. Kept all interpolation arguments polynomial until shared zeros were addressed.
7. Added precise historical context, finite-check scope, and formalization status.

The final reader caught a notation typo in the entry valuation: a comma after `-e` was replaced by multiplication spacing. One inline Vandermonde identity was displayed to remove an overfull line. Neither correction changes the theorem or estimates.

## Source identity

The 29 recovered research files match the Git blob SHA-1 values returned by explicit-commit GitHub retrieval. SHA-256 hashes and sizes are in `provenance/source-manifest.json`. One historical JSON has no terminal newline; its exact original bytes are preserved.

The analytic review read an earlier exported pure candidate whose SHA-256 was `ea0b193954e83afa6f715eb4296df29397d28b3dced4e73dd120343129dcd588`. The commit-pinned file has SHA-256 `36450caaf25991a5bda13e681d84272c3f9a023a3abafc23ad0be84ed40c7539`; the only difference is an additional trailing newline in the earlier export. The arithmetic reviewer read the commit-pinned mathematical text. Source authentication was performed editorially after their reviews, and is not retroactively attributed to the reviewers.

## Rendering and reproducibility

The PDF contains 14 US Letter pages, 11-point Computer Modern/Latin Modern text and mathematics, 1.05-inch margins, numbered sections/equations, and dark-blue navigation links. It was compiled twice after the final corrections. The final build has no overfull/underfull boxes, unresolved references, or warnings.

Every page was rendered at 100 dpi and visually inspected in page-pair images. The inspection covered title/abstract/contents, theorem page, all dense proof pages, section transitions, and references. No clipped equations, colliding text, broken page numbers, or overflowing bibliography entries were found. Rendering images are temporary QA material, not research evidence.

Finite replays: 100 conservative normalizations; 40 independent rational content checks; 144 direct functional comparisons; 36 exact determinant evaluations; 12 primitive nonzero enclosures; and the additional p=2,K=48 enclosure. All passed. These are finite implementation checks, not formal theorem verification.

The workflow configuration has not been remotely run in the target repository at preparation time. Publication is a separate action from local build and review.
