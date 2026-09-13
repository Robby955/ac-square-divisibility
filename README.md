# Explicit AC constructions for divisibility subfamilies draft

# Paper in progress

**Robert Sneiderman — Independent**

Contact: [robbysneiderman@gmail.com](mailto:robbysneiderman@gmail.com).

With **GPT-6 Astra (OpenAI)**, AI research collaborator.

Let u,y be free generators. For integers p,s, define the ordered pair of
relator words

```math
G(p,s)=\left(u^2y^{-(2s+1)},\;uy^puy^{-s}u^{-1}y^{-p}\right).
```

Setting both words equal to the identity gives the relations

```math
u^2=y^{2s+1}\qquad\text{and}\qquad uy^pu=y^puy^s.
```

We call this the square family because the first relation contains u².
The parameters p,s choose a member of the family; they are not additional
generators. G denotes the specified relator
pair on which Andrews–Curtis moves act.

This note proves ordinary, fixed-rank Andrews–Curtis triviality when p and s
are natural numbers and p divides s or s+1. In particular, every
G(2,s) with nonnegative s is covered. The quantified proof also includes two
arithmetic root families for integer p and a nonnegative quotient.

[Read the paper](paper/square-divisibility.pdf). Its source is
[main.tex](paper/main.tex). See [the release notes](RELEASE_NOTES.md),
[citation metadata](CITATION.cff), and [contribution statement](CONTRIBUTIONS.md).
The main proof consists of a fixed entry route,
a recursive doubling witness and two explicit finishes. All substitutions
restore the donor relator, and every basis transport includes its final
ordinary AC correction.

The entire square family remains open here. The next degree-three target is
G(3,3m+1); its companion restoration remains unproved, beginning at d=2.
The package states that restoration as a hypothesis and proves the resulting
equivalence. It does not assume it, solve AK(3), or settle AC or Stable AC.

This is ongoing research only recently started, the paper is in draft form and requires substantial revision.

## Reproduce the finite certificates

Python 3.10 or later, standard library only:

```sh
python3 verify.py
python3 experiment.py --matrix --output run/replay.json
python3 experiment.py --p 6 --s 23 --output run/p6-s23.json
```

The fixed matrix contains 50 distinct presentations. All 50 replay with
limits removed; 48 satisfy the frozen golden budgets. Cases (2,11) and
(2,12) exceed the work budget. The six frozen comparison certificates are
replayed independently; this construction improves none of their lengths.
See [the full receipt](receipts/replay.json) for paths, hashes, work, peak
length and timings. These are construction measurements, not new challenge
solves or shortestness claims.

The proof contribution and discovery-track competition have separate purposes.
The competitive archive must retain its shortest verified certificates.
Paths generated for this paper are proof evidence; they do not replace a
shorter certificate or count as a score improvement. Any candidate transferred
to the scored campaign must first be replayed under that track's limits and
compared with the controller's current best path.

The finite CLI accepts p,s in 0..100 and quotient at most 8. The bound prevents
accidental large exports from an exponential witness constructor. It does
not restrict the theorem. There is no search, policy inference, or model
download in reproduction.

## Check the quantified theorem

Install Lean through elan if it is not already available. From this root:

```sh
cd lean
lake exe cache get
lake build
cd ..
python3 verify.py --lean
```

The first dependency setup requires network access. The pinned toolchain is
Lean 4.29.1; Mathlib and its transitive revisions are in
[lake-manifest.json](lean/lake-manifest.json). Verification checks dependency
commits and tracked-file cleanliness. It builds the focused package and runs
three strict trust-zero Lean commands, collecting 59 logical-dependency
reports. Those reports admit only propext, Classical.choice and Quot.sound.
There are no supplied conjecture assumptions or proof escapes.

The existing tested receipt is [verification.json](receipts/verification.json).
The local preparation run reused the existing pinned Mathlib package cache;
it did not perform a fresh network bootstrap. Each paper-specific Lean
module was built in the package's separate build directory. Build caches
and local symlinks are excluded from the repository artifact.

The main declaration is
`AC.MillerSchupp.SquareFamily.P2.divisibility_square_solvable` in
[ACSquareP2Families.lean](lean/ACSquareP2Families.lean).
The root construction is in [ACSquareP2Root.lean](lean/ACSquareP2Root.lean),
the exact entry is in [ACSquareP2Entry.lean](lean/ACSquareP2Entry.lean), and
the unresolved induction interface is in [ACSquareHalving.lean](lean/ACSquareHalving.lean).
The complete dependency closure is included; sibling research folders are
not needed.

Lean proves the quantified theorem. Python is a separate executable
implementation, and each emitted path is certified by exact official replay.
It is not extracted from Lean; equality of the complete factor lists across
the two implementations has not been proved. The formal theorem does not
depend on the finite replay matrix.

## Compile the paper

With a standard TeX Live installation containing the packages used in the source:

```sh
python3 paper/generate_table.py
python3 paper/check_exposition.py
cd paper
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build main.tex
```

The shipped PDF was compiled and its pages were visually inspected. It
explains the entry's two donor substitutions, gives a doubling diagram, and
derives both arithmetic finishes. The complete 51-row schedule remains in
[entry_route.json](entry_route.json) and its generated
[typeset listing](paper/entry-table.tex). The transcription check exercises
the displayed identities at signed parameters; it is not a quantified proof.

Section 5 states the pinch, mirror/sign, complementary-height and parameter
shear transports as lemmas, then displays the four-factor period
identity. The residue corollaries follow from those witnesses; height four
also uses the existing finite seed. A separate elementary group calculation
checks that the square presentations define the trivial group. It supplies
no new AC path. The new transport statements restate the existing formal
constructions, with their factor lists checked by the exposition script.

[REVIEW_RESPONSE.md](REVIEW_RESPONSE.md) records the response to the supplied
manuscript review, including the forward automorphism direction and the
distinction between construction length and shortest-path complexity.

## Repository checks and release assets

[The verification workflow](.github/workflows/verify.yml) builds Lean, checks
source hashes and logical dependencies, runs the Python tests, replays the
fixed matrix, and checks regeneration of the appendix table. Action revisions
are pinned. [Hosted verification of v0.1.0 passed](https://github.com/Robby955/ac-square-divisibility/actions/runs/34726565443).
The [versioned release](https://github.com/Robby955/ac-square-divisibility/releases/tag/v0.1.0)
preserves the submitted proof package and its full source commit.

To prepare the files for a GitHub release from a clean committed version:

```sh
python3 prepare_release.py --output run/release
```

The command creates the PDF, a source archive, release notes, the full source
commit, and SHA-256 checksums. It does not create a tag or publish anything.
The release owner uploads these assets and records the same full commit in
the SAIR proof contribution. No arXiv account is needed to link this PDF.

The original code and repository documentation use [Apache 2.0](LICENSE).
The paper uses [CC BY 4.0](paper/LICENSE). See [NOTICE.md](NOTICE.md) for
third-party attribution. These are the prepared release terms; the controller
retains the public release decision.

## Contribution and provenance

[PRIOR_WORK.md](PRIOR_WORK.md) records the focused comparison and its limits.
The contribution is an explicit arithmetic construction, quantified Lean
proofs and independently replayable exports. Priority for the underlying
AC-triviality classes has not been established; this is not the first AC
formalization or certificate verifier.

The proof sources come from commit
`68ceae3d422eee6de28bfd54793b21b2031cbda3` of the preserved research worktree.
[SOURCE_PROVENANCE.json](SOURCE_PROVENANCE.json) records the source hashes
and extraction boundaries. The package has a separate release history.
Its Git commit identifies the submitted package version; the proof-source
commit above is provenance, not a substitute for that release commit.

The official AC definitions and verifier are pinned to SAIR commit
`99a65377c5c4f412cd9af7b8d31c41464a855736`. Their Apache 2.0 license is retained
in [lean/OFFICIAL-LICENSE](lean/OFFICIAL-LICENSE) and
[official_verifier/LICENSE](official_verifier/LICENSE). The copied verifier
core and canonicalization module are unchanged.

Research used GPT-6 Astra through Codex and additional Fable assistance.
[CONTRIBUTIONS.md](CONTRIBUTIONS.md) records their roles and the limits of the
available historical model identification. Existing finite solved instances
and baseline certificates retain their prior credit.
