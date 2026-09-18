# Contributor Network draft — review before submission

Not submitted. This description is generated from the exact release commit. Confirm that the commit and paper are publicly accessible before using it.

Conjecture: **AC**
Direction: **proof — partial result**
Repository: https://github.com/Robby955/ac-square-divisibility
Full commit: `{{SOURCE_COMMIT}}`
Paper: https://github.com/Robby955/ac-square-divisibility/blob/{{SOURCE_COMMIT}}/paper/square-divisibility.pdf

## Description

This contribution gives explicit ordinary rank-two Andrews–Curtis constructions for the ordered square presentations

\[
G(p,s)=(u^2y^{-(2s+1)},\;uy^puy^{-s}u^{-1}y^{-p}).
\]

The original construction proves AC-triviality for nonnegative p,s whenever p divides s or s+1. This update extends the all-integer-degree low-height result to height five: every G(p,5), p in Z, is ordinarily AC-trivial. A 1,285-move residual certificate, the previously proved root reduction, and sign/period transports supply the result. The new quantified theorem and its residual seed are checked in Lean. The executable addition exports complete paths from the literal square presentations, including the entry and ordinary basis correction.

The update also gives a period transport G(p,s) -> G(p+2s+1,s) with two multiplications and nine arbitrary-word primitives. The construction is formalized. A separate written proof establishes that two multiplications are optimal for s >= 1, even without a fixed-donor restriction. The paper also proves that the missing degree-three companion restoration cannot preserve the original root normal closure; that does not exclude unrestricted restoration.

The 28 original proof-source modules and the official definition/verifier pins remain unchanged. Local validation includes four trust-zero Lean checks and 71 logical-dependency reports, the original 50-case replay matrix, and 281 added exact replays. The multiplication lower bound and the restoration obstruction are written proofs, not additional formalized claims. Python is a separate implementation rather than extracted Lean code.

This is not a solution of the full square family, the degree-three restoration, H, AK(3), AC, or Stable AC. Literature priority for the underlying triviality classes and live discovery-track first-solver eligibility have not been established. No new benchmark-first or shortest-complete-path claim is made.

## Prior work used

- A. Shehper et al., *What makes math problems hard for reinforcement learning: a case study*, arXiv:2408.15332v2. Their established Miller–Schupp families, including MS(1,w), and substitution operations provide context. Their theorems are credited, not claimed anew.
- P. Panteleev and A. Ushakov, *Conjugacy search problem and the Andrews–Curtis conjecture*, arXiv:1609.00325. Products of conjugates and the treatment of generator automorphisms are established techniques used here with explicit witnesses and basis corrections.
- R. Sklinos, *On ampleness and pseudo-Anosov homeomorphisms in the free group*, arXiv:1409.8599v1, Theorems 2.10–2.11. Used for the standard amalgam normal-form/conjugacy theorem in the written restoration obstruction.
- SAIR shared ordinary AC definitions and verifier, pinned to `99a65377c5c4f412cd9af7b8d31c41464a855736`. These are reused unchanged with their licenses and source attribution.
- The earlier project release v0.1.0 and the supplied height-five/period research notes are the direct development sources. The supplied residual list is preserved unchanged; this version adds its formal integration, complete square exports, and revised exposition. Additional contextual references and comparison limits are in the paper and PRIOR_WORK.md.

Robert Sneiderman is the responsible author. AI assistance in exploration, implementation, formalization, and writing is disclosed in the paper and CONTRIBUTIONS.md.

## Submission reminder

SAIR's Proof Track rules were read during preparation. They accept partial results and require the full commit with a GitHub link. Submission automatically shares the contribution publicly and requires the author's sharing agreement. No sharing agreement or submission is made by this draft.
