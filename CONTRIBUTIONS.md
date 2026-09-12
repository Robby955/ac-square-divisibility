# Contributions

**Robert Sneiderman — Independent.** Research direction, choice of problems,
scope and claim decisions, coordination of proof and certificate work, and
responsibility for the version selected for public release.
Contact: [robbysneiderman@gmail.com](mailto:robbysneiderman@gmail.com).

**GPT-6 Astra (OpenAI) — AI research collaborator, through Codex.**
Mathematical exploration, development of explicit word identities and witness
constructions, Lean and Python implementation, manuscript drafting and
revision, and organization of reproducible evidence. The title-page credit
identifies the system as AI; OpenAI is its developer, not an affiliation or
endorsement of the human author. Earlier Codex work is credited as recorded
in the source history without assigning an unverified model version to every
historical session.

**Fable — additional AI research assistance.** The preserved square-family
analysis identified the quotient-two pinch and explained the earlier p=±1
entry into the published MS(1,w) class. Its computational checks and prior-work
comparison informed the subsequent proof development. No provider or exact
model identity beyond the supplied Fable session record is inferred here.

The mathematical sources and existing certificate materials used in the work
are cited in the paper and PRIOR_WORK.md. Lean checks proof terms against the
stated definitions; independent numbered replay checks the exported paths.
Neither constitutes an external assessment of novelty or publication merit.

## Construction provenance

The available history supports the following attribution. Commit identifiers
below refer to the preserved research source repository, not to commits in
this extracted publication repository.

- **Quotient-two pinch and the p=±1 link to MS(1,w):** Fable's preserved
  square-family analysis, supplied to Sneiderman before the divisibility
  development. The published MS theorem retains its authors' credit.
- **Uniform root entry:** Codex-assisted proof-development pass under
  Sneiderman's direction; `ACSquareP2Entry.lean` and research commit
  `502cd9b98bf1daf9d5f8450aaa0664e13302cc8f`.
- **Iterated doubling and the second arithmetic finish through B_(p−1):**
  the same development pass; `ACSquareP2Root.lean`, in that commit.
- **Shifted halving, C_d/D_d, and the exact restoration condition:** later
  Codex-assisted pass; `ACSquareHalving.lean` and research commit
  `47f5dca4c02c062cd1ccbf5189f2e876af15ef0e`. Restoration remains unproved.

The commits locate the work; they do not establish an individual discovery
timestamp for every identity or the exact model used in each historical
session. No such finer attribution is inferred. A manuscript review supplied
by Sneiderman informed the subsequent exposition revision; its reviewer
identity was not provided. It is not represented as a referee report.

The author line, contributor credit and citation metadata are intended to
remain consistent. Any later venue-specific authorship requirements should
be checked for that venue. The present artifact is a research note prepared
for GitHub and the SAIR Contributor Network, not an arXiv submission.
