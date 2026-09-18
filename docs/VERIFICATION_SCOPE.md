# Verification scope for v0.2.0-rc1

This document distinguishes quantified proofs, finite path replay, written arguments, and public-release status.

## Quantified Lean results

The 28 original modules are frozen at their SOURCE_PROVENANCE hashes. The original divisibility theorem, entry, basis corrections, and existing parameter transports were rebuilt without changing those sources.

New modules check the residual seed (encoded segments, using `decide +kernel`), every integer degree at square height five, the two original-coordinate slices, and the uniform two-factor period construction. `ReleaseChecks.lean` adds twelve logical-dependency reports to the original 59. All four report files run with `--trust=0`; allowed dependencies are only `propext`, `Classical.choice`, and `Quot.sound`.

The multiplication-optimality argument and the uniform root-normal restoration obstruction are written proofs. They are not additional Lean-checked statements. No formalization claim is made for the broader 110-page collection or later donor-changing notes.

## Finite replay

The copied official `AC.lean`, `core.py`, and `canon.py` retain their original pins. The pinned verifier is run **locally**; this is not live organizer verification or an accepted competition submission.

The old 50-case arithmetic matrix is unchanged. The new 281-case matrix checks the residual seed, 33 complete square-height-five paths, and 247 literal period transports. A separate signed-letter interpreter anchors endpoints independently and recomputes path metrics.

A complete square path includes the affine entry, transported root solution, and ordinary correction of the image basis. The residual seed alone does not include those stages. Period transports do not end at the standard basis and are not called trivializations.

Python is not extracted from Lean. A finite exported list is checked in its own right; no general theorem identifies all Python-generated factor lists with the formal lists.

## Reproduction versus discovery

Reproduction runs no heuristic search, downloads no model, and needs no GPU. The new seed is imported unchanged from the supplied first-extension bundle. Its source JSON SHA-256 is recorded in `receipts/v020/additions-replay.json`. `generate_release_lean.py --check` verifies exact regeneration of the kernel-checkable data.

The only network work required for a clean formal build is installing the pinned toolchain and dependencies. The fresh integration build downloaded the pinned Mathlib cache; the frozen baseline worktree reused that dependency cache but had its own project build directory.

## Remaining boundaries

No global literature-priority review, independent referee assessment, live first-solver check, hosted CI run of this unpublished candidate, tag, public release, or Contributor Network submission is claimed. The review branch is not a complete proof of AC, Stable AC, the square family, the degree-three restoration, H, or AK(3).
