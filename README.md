# Explicit Andrews–Curtis Constructions for Square Presentations

**Robert Sneiderman — Independent Researcher**
**Release candidate: v0.2.0-rc1.** Prepared for review; not a complete proof of the Andrews–Curtis conjecture.

[Read the paper](paper/square-divisibility.pdf) · [LaTeX source](paper/main.tex) · [Verification scope](docs/VERIFICATION_SCOPE.md) · [Release notes](RELEASE_NOTES.md)

For free generators `u,y`, this project studies the specified ordered pair

```math
G(p,s)=\left(u^2y^{-(2s+1)},\;uy^puy^{-s}u^{-1}y^{-p}\right).
```

Ordinary Andrews–Curtis moves invert a relator, multiply it by the other relator, or conjugate it. The rank stays two. A proof that the associated group is trivial is not, by itself, an ordinary path from these words to the standard pair.

## Results

For nonnegative integers `p,s`, the divisibility construction proves ordinary AC-triviality when `p` divides `s` or `s+1`. It includes every `G(2,s)` with nonnegative height.

For **every integer degree `p`**, the square family is also solved at heights **three, four, and five**. Height five is the extension in this release: a kernel-checked residual seed, together with the existing arithmetic, sign, and period transports, covers all eleven degree residues. The new executable constructor exports complete paths from the literal square presentations, including the entry and basis correction.

The new period path `G(p,s) -> G(p+2s+1,s)` uses **two relator multiplications and nine mathematical primitives**. The construction and its factor count are formalized. The paper separately proves that two multiplications are optimal for `s >= 1`; that lower-bound argument is not formalized in this release.

The remaining degree-three family `G(3,3m+1)` still requires a companion restoration, beginning at `d=2`. The paper explains why this cannot preserve the original root normal closure. That is a restriction on a strategy, not an obstruction to unrestricted AC-triviality. This release does not solve the full square family or the AC and Stable AC conjectures.

## Reproduce the finite checks

Python 3.10 or later; standard library only:

```sh
python3 verify.py
python3 experiment.py --matrix --output run/replay.json
python3 release_additions.py --matrix --output run/additions.json
python3 verify_additions.py run/additions.json
python3 generate_release_lean.py --check
python3 paper/check_exposition.py
```

The original matrix has 50 cases: all pass unlimited pinned-verifier replay and 48 meet its recorded resource limits. The original `(2,11)` and `(2,12)` paths exceed the work limit. No existing shorter comparison path is replaced.

The addition matrix has 281 paths: one residual seed, 33 complete height-five paths for degrees `-16` through `16`, and 247 signed or illustrative period paths. All 281 pass both unlimited replay and the recorded limits. A separate interpreter anchors every endpoint to its formula and recomputes the costs. Finite tests are not a substitute for the quantified proof.

To export a complete signed height-five example:

```sh
python3 release_additions.py --height5 -4 --output run/height5-minus4.json
```

The command requires `--allow-large` when the absolute value of `p` exceeds 100. This resource guard does not restrict the theorem. Period certificates have a nonstandard target and are transports, not challenge solves.

## Check the Lean proofs

Install Lean through elan, then use the pinned project:

```sh
cd lean
lake exe cache get
cd ..
python3 verify.py --lean
```

The toolchain is Lean 4.29.1; [the manifest](lean/lake-manifest.json) pins Mathlib and all transitive dependencies. A clean dependency bootstrap requires network access. The focused build is followed by four `--trust=0` checks and 71 logical-dependency reports. The only admitted logical dependencies are `propext`, `Classical.choice`, and `Quot.sound`.

The 28 original proof-source modules are unchanged and are still checked against [SOURCE_PROVENANCE.json](SOURCE_PROVENANCE.json). The new modules are:

[ACSquareHeightFiveSeed.lean](lean/ACSquareHeightFiveSeed.lean) kernel-checks the 1,285-move residual certificate. [ACSquareHeightFive.lean](lean/ACSquareHeightFive.lean) proves all integer degrees at height five and the exponent-ten and exponent-eleven slices.

[ACSquarePeriodTwo.lean](lean/ACSquarePeriodTwo.lean) proves the uniform two-factor period and nine-primitive path. [ReleaseChecks.lean](lean/ReleaseChecks.lean) records the additions' logical dependencies.

The full main height-five declaration is `AC.MillerSchupp.SquareFamily.HeightFive.square_five_all`. The original divisibility declaration is `AC.MillerSchupp.SquareFamily.P2.divisibility_square_solvable`.

The seed's generated Lean data are not trusted solver output: every segment is checked by the kernel against the existing certificate soundness theorem. Python is a separate implementation, not extracted from Lean. Each finite exported list is certified by its own exact replay.

## Paper and proof data

The focused paper includes the definitions, both original arithmetic finishes, exact entry and basis corrections, the complete 51-row affine schedule, the height-five proof, the improved period and its optimality proof, and the precise restoration restriction. The original four-factor period is retained in an appendix because the frozen construction and its measurements use it.

AI assistance is disclosed in the acknowledgments and [contribution record](CONTRIBUTIONS.md), not presented as an institutional affiliation or endorsement. [PRIOR_WORK.md](PRIOR_WORK.md) records the scope of the source comparison. Literature priority and live first-solver eligibility are not established.

Compile the paper with a TeX Live installation containing its declared packages:

```sh
python3 paper/generate_table.py
cd paper
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build main.tex
```

The complete entry is [entry_route.json](entry_route.json). The unchanged residual certificate is [G4_5_residual_letter.json](certificates/G4_5_residual_letter.json). Version-specific receipts are under [receipts/v020](receipts/v020); the original receipts remain in place. The larger research collection and later donor-changing diagnostics are separate supplements, not dependencies of this focused release.

## Review and release

This candidate is staged separately from `main` and preserves `v0.1.0`. [The checklist](docs/RELEASE_CHECKLIST.md) distinguishes completed local checks from the remaining human review, public push, hosted CI, and Contributor Network submission.

From a clean committed checkout, prepare version-bound assets locally:

```sh
python3 prepare_release.py --output run/release
```

This creates the PDF, source archive, full source commit, release notes, checksums, and a draft Contributor Network description. It does **not** push, tag, publish, or submit. The draft must be reviewed, and its commit must be publicly accessible before submission. The proof contribution is separate from the discovery-track scoring archive.

The release manifest hashes staged/tracked files. After an intentional edit, stage the intended files and run `python3 refresh_manifest.py`, then stage the updated manifest. This command refuses drift in the frozen original Lean modules and never rewrites their provenance pins.

## Licenses and provenance

Original code and repository documentation use [Apache 2.0](LICENSE); the paper uses [CC BY 4.0](paper/LICENSE). Third-party licenses and attribution remain in [NOTICE.md](NOTICE.md).

The original research-source commit is `68ceae3d422eee6de28bfd54793b21b2031cbda3`. The integration baseline is `16fd2c61570161f5fb5856d2e1d5c7fd67ee3a34`. The official definition and verifier are pinned to SAIR commit `99a65377c5c4f412cd9af7b8d31c41464a855736`. These identifiers have different purposes; the release assets record the exact candidate commit separately.
