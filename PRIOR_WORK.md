# Focused comparison of the divisibility construction

Reviewed September 12, 2026. The exact arithmetic statement and its explicit
root reduction were compared with the following primary sources. This is a
bounded comparison, not an exhaustive priority determination.

Ali Shehper, Anibal M. Medina-Mardones, Lucas Fagan, Bartłomiej Lewandowski,
Angus Gruen, Yang Qiu, Piotr Kucharski, Zhenghan Wang and Sergei Gukov,
[*What makes math problems hard for reinforcement learning: a case study*](https://arxiv.org/abs/2408.15332v2); see Theorem B.
Theorem B and its component results supply the nearest stated infinite
families. The earlier p=1 analysis uses their Theorem 2. Their substitution
method is prior work. This package gives its own finite witnesses for the
divisibility construction; it does not claim an independent new general
substitution technique. The exact divisibility statement was not identified
in those theorem statements. Unexamined coordinate equivalences could still
relate it to a previously solved class.

Pavel Panteleev and Alexander Ushakov,
[*Conjugacy search problem and the Andrews–Curtis conjecture*](https://arxiv.org/abs/1609.00325).
Their conjugacy and substitution framework, including the treatment of
automorphisms in Section 3, precedes the present work. An invertible change
of coordinates or a supplied product of conjugates is therefore not a novelty
claim here. The package makes its particular witnesses and final basis
corrections explicit.

Marc Lackenby,
[*The stable Andrews-Curtis conjecture and thickenable presentations of the trivial group*](https://arxiv.org/abs/2606.06122v1); see Theorem 1.3.
Theorem 1.3 establishes ordinary AC triviality for thickenable balanced
presentations of the trivial group. The present comparison does not establish
whether every divisibility presentation is in that class. No claim to lie
outside the geometric theorem is justified by this review. Its treatment of
generator moves also prevents claiming automorphism elimination as new.

Caroline Zhang, Aaron Zhou, Robert Joseph George, Sergei Gukov and Anima
Anandkumar,
[*AI-Driven Mathematical Discovery for the Andrews–Curtis Conjecture*](https://openreview.net/forum?id=lt3Lpa4d2d),
NeurIPS 2025 MATH-AI workshop. The indexed abstract and official workshop
record describe prior Lean formalization and an ACC autoformalizer. The full
OpenReview text was blocked by a browser-verification page in this review.
That limits detailed theorem comparison, but the earlier formalization
itself is sufficient to exclude any first-formalization claim here.

Lucas Fagan, Michele Tarquini, Ali Shehper, Maksymilian Manko, Angus Gruen,
Coco Huang, Giorgi Butbaia, Davide Passaro and Sergei Gukov,
[*The Two-Hump Problem: Bridging the Difficulty Gap in Mathematical Reinforcement Learning*](https://arxiv.org/abs/2606.21611v1),
and the accompanying [ACSolverX repository](https://github.com/Math-AI-Caltech/ACSolverX).
The earlier research comparison found the covered finite instances in the
Caltech solved materials where the finite table reaches. We reuse six frozen
paths as baselines, not as newly discovered solutions. This package neither
uses pretrained inference nor adds finite benchmark solves.

Josep Carreras,
[*Machine-checkable equivalence certificates at the length-14 Andrews-Curtis frontier*](https://arxiv.org/abs/2607.23611).
The concrete equivalences in its stated theorems are additional precedent
for machine-checkable AC certificates. They do not state the divisibility
construction in this note. This observation is confined to the stated
theorems, and is not a claim that all possible equivalences were excluded.

The shared formal definition and ordinary replay implementation are reused
from [SAIR's pinned repository](https://github.com/SAIRcompetition/Andrews-Curtis/tree/99a65377c5c4f412cd9af7b8d31c41464a855736).
Those components retain their source identity and license. The contribution
to present for community review is the explicit divisibility construction,
its proved parameter consequences, and the exact unresolved restoration
interface. Determining the strongest novelty claim remains an appropriate
question for expert review; it is not necessary to label this a complete
proof of either conjecture to share the scoped result.
