# Response to the supplied manuscript review

September 12, 2026. This responds to the review supplied by Robert Sneiderman
of the earlier eight-page manuscript. The reviewer's identity and review
process were not supplied. Its favorable assessment is not used as evidence
of priority or represented as independent referee validation.

## Mathematical exposition

The revised abstract separates the result from its certification. Section 1
defines the square presentation as relations as well as an ordered tuple,
introduces P(n,a,b,c), and gives the two quotient-two transfers. Section 5.1
derives the pinch identities, complementary-height transport and c-shear.

Section 3 explains the two donor substitutions behind the entry, including
their exact negative conjugate factors. Temporary coordinate changes explain
the cancellations; the frozen 61-primitive schedule eliminates them from the
ordinary path. The complete 51-row listing remains in entry_route.json and
paper/entry-table.tex, with hashes in MANIFEST.json. It is no longer inserted
as two dense pages of the paper.

Section 4 contains a doubling diagram and an expanded two-case proof. The
second case now derives the intermediate companion q, its substitution for
y^p, the identity producing B_(p−1), and the final negative-power doubling.
The use and restoration of each donor are stated at the point of use.

## Suggestions that required correction

The forward automorphism direction is f, not f inverse. The entry ends at
f(B_p,A_s), so a root solution gamma transports to f(gamma), followed by the
ordinary correction of (f(u),f(y)). The inverse map belongs to the converse
argument. Section 3 now displays the forward path and explains the converse.
There is one appropriate basis correction per direction.

The exponential factor count is a count of this construction. It is not a
lower bound on the shortest path. Bridson's cited lower-bound results begin
in rank four; we do not claim a corresponding rank-two complexity theorem.

Agreement of Lean and Python lists on finitely many parameter values would
not identify the implementations for all parameters. Section 6 instead
states the existing verification responsibilities exactly: Lean proves the
quantified result; Python is a separate implementation, and official replay
certifies each exported path. No extraction or universal list-equality
theorem is asserted.

## Costs, literature and attribution

Section 2 gives one display for witness factors, mathematical primitives and
official numbered moves, then defines official work. Negative witness
factors retain two donor inversions in this exporter. The 61 entry
primitives, the seed's 81 primitives, and the full example path counts are
explicitly distinguished.

The paper and PRIOR_WORK.md add Miasnikov–Myasnikov's length-at-most-twelve
classification, Lisitsa's ATP constructions and parametric conjectures, and
Bridson's complexity results. The comparisons use primary publication
records. They do not resolve overlap with prior MS families or Lackenby's
thickenable class. Priority remains unestablished.

CONTRIBUTIONS.md now maps the entry, doubling, second-case finish, and
halving/restoration interface to the recorded development passes. Fable's
pinch and MS(1,w) connection retain their credit. The available records do
not support assigning a separate discovery attribution to every identity.

## Scope and verification

The divisibility theorem and existing parameter consequences are unchanged.
The general square family and the d=2 companion restoration remain open.
No longer proof path replaces a shorter leaderboard certificate.

The new paper/check_exposition.py checks the added display identities and
cost formulas on signed inputs. During revision it caught and corrected a
sign error in the newly written c-shear explanation: the displayed shear
sends c to c−t. The pinned Lean proof was unchanged. These finite checks are
transcription safeguards, not proofs of additional parameter coverage.

Reproduction and prior verification remain available through verify.py and
experiment.py. The PDF compile and exposition-check receipts accompany this
revision. Public repository creation, hosted CI, the public release and any
SAIR contribution remain controller actions; this revision publishes nothing.
