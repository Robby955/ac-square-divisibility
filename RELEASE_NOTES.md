# v0.2.0-rc1 — square-family constructions

This is an unpublished review candidate, not a complete proof of AC or a first-solver announcement.

## Mathematical additions

The height-five result now has a quantified Lean theorem covering every integer degree. Its 1,285-move residual seed is replayed by the kernel, and the original-coordinate consequences `P(10,5,b,c)` and `P(11,a,6,c)` are formalized. The new Python exporter includes the complete affine entry and ordinary basis correction; it does not mistake the residual seed for a complete square path.

A new uniform period transport uses two multiplications and nine mathematical primitives, replacing the four-factor schedule for the new exports. Its construction and cost are formalized in a separate module. The written multiplication-optimality theorem for positive height does not claim optimal letter length or work.

The focused paper includes the uniform root-normal obstruction to the missing restoration, with its proof and scope. That obstruction is not formalized here and does not rule out unrestricted AC paths.

## Writing and release structure

The revised paper uses a conventional author block, a common set of definitions, a linked contents page, complete argument chains, and a single verification/provenance section. AI assistance remains disclosed in the acknowledgments and contribution record. The complete 51-row affine entry schedule is printed in the appendix, and the old four-factor period remains available there with its historical verification context.

The 110-page research compilation and subsequent donor-changing diagnostics remain separate supporting work. They are not silently incorporated into the formal claims of this square-family release.

## Validation

The original 28 proof-source modules, dependency revisions, official definition, and copied official verifier are preserved. The frozen v0.1.0 baseline was rebuilt. The review candidate adds four Lean modules, twelve logical-dependency reports, twelve Python tests, and a 281-path replay matrix. The full check has 21 Python tests and 71 logical-dependency reports across four trust-zero check files. Version-specific receipts under `receipts/v020` distinguish executed checks from remaining public-release actions.

All 281 added paths pass the pinned verifier with and without the recorded limits. The original matrix remains 50 unlimited passes and 48 passes under the recorded limits. The original `(2,11)` and `(2,12)` paths exceed the work budget; none of the six frozen shorter comparison paths is replaced.

The stale README hash on the integration baseline was repaired by regenerating the release manifest after intentional staging. Frozen proof-source pins were not changed. The seed's source JSON is retained unchanged; its Lean segments are generated deterministically and kernel-checked.

## Remaining scope

The release does not solve the full square family, the degree-three restoration, H, AK(3), AC, or Stable AC. Literature priority, live first-solver eligibility, external referee approval, and hosted CI of this unpublished candidate are not claimed. No push, public tag, release publication, sharing agreement, or Contributor Network submission is performed by local preparation.

`prepare_release.py` generates assets from a clean commit and inserts that full commit into a draft contribution description. The author must review and approve publication and submission separately.

## Preserved baseline

The public v0.1.0 tag remains at `d0ed2c06bb3a9e7ed31e2f31e24d17de6323efe8`. Its original release notes, paper, formal sources, and measurements remain accessible at that tag. The review branch starts from `16fd2c61570161f5fb5856d2e1d5c7fd67ee3a34`, whose intervening changes were to README exposition.
