# v0.2.0-rc1 review checklist

The candidate is prepared on an isolated review branch. A prepared asset is not a public release.

## Local release gates

- Rebuild the frozen v0.1.0 baseline and preserve its original proof-source and official-verifier pins.
- Build the new quantified height-five theorem and two-factor period in the pinned Lean project; run all trust-zero report files.
- Run the original and new unit tests; replay the original 50-case and new 281-case matrices.
- Check deterministic generation of the Lean seed and the original affine table.
- Compile the focused paper and inspect rendered pages for equations, clipping, and unresolved references.
- Refresh the release manifest only after staging the intended files. Re-run `verify.py --lean` against the final manifest.
- Commit the review candidate locally and generate assets bound to that full commit.

The receipts under `receipts/v020` and the release asset summary record which gates have actually completed. A checklist entry is not itself proof of completion.

## Human/public gates — not performed by preparation

1. Review the theorem scope, written lower-bound and quotient arguments, acknowledgments, and source comparison.
2. Review the Git diff and approve the candidate for pushing. Do not overwrite v0.1.0 or force-push main.
3. Push the review branch and inspect hosted CI on the exact candidate commit.
4. After approval, publish the selected release and its PDF/source assets. Use the public full commit hash in the contribution.
5. Review the generated Contributor Network description and explicitly approve public sharing and submission.

The submission direction is AC / proof **partial result**, not a complete proof claim. The source rules require an accurate full commit with a repository link and disclose that Contributor Network entries are publicly shared; recording an entry does not certify correctness.
