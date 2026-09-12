# Version 0.1.0 — divisibility construction

The paper proves ordinary rank-two AC triviality of G(p,s) for natural p,s
such that p divides s or s+1. This includes G(2,s) for every nonnegative s.
It gives a complete affine entry route, recursive doubling witnesses, and
two arithmetic finishes, with corresponding Lean declarations.

The release includes the PDF and LaTeX source, a pinned Lean project, the
numbered-path constructor, unchanged official verifier sources, full replay
receipts, prior-work comparisons, citation metadata, and file hashes.

Local validation passes nine Python tests, 59 logical-dependency reports,
three strict trust-zero checks, and 50 unlimited official replays. Of the
50 replay cases, 48 meet the frozen golden budgets. On the six frozen
certificate overlaps, this construction improves no path lengths.

The remaining square family is open. The degree-three induction requires
companion restoration at d=2,4,8,...; the d=2 case is unresolved. Priority
for the underlying AC-triviality classes has not been established.

These proof certificates are separate from the discovery-track submission
archive. The scored campaign retains its shortest verified certificates.
This release does not claim a leaderboard gain or replace shorter paths.

`SOURCE_COMMIT.txt` identifies the exact repository version used to produce
these assets. `SHA256SUMS` records the PDF, source archive and release-note
hashes. The GitHub verification workflow is configured; no hosted result is
claimed before its first successful run.
