"""Finite normal-closure witness algebra and charged AC move compiler.

Extracted unchanged from the recorded research source; see SOURCE_PROVENANCE.json.
"""
from __future__ import annotations
from dataclasses import dataclass
import word_engine as raw
Word = tuple[int, ...]
Factor = tuple[Word, bool]
X, Y = (1,), (2,)

def reduce_word(word) -> Word:
    return tuple(raw.reduce_word(word))


def inv(word: Word) -> Word:
    return tuple(-x for x in reversed(word))


def mul(*words: Word) -> Word:
    return reduce_word(x for word in words for x in word)


def power(word: Word, exponent: int) -> Word:
    return mul(*((word if exponent >= 0 else inv(word)),) * abs(exponent))


def conjugate(g: Word, word: Word) -> Word:
    return mul(g, word, inv(g))


@dataclass(frozen=True)
class Witness:
    """Exact ambient free-group identity source * product(factors) = target."""

    source: Word
    target: Word
    factors: tuple[Factor, ...]

    @classmethod
    def refl(cls, word: Word) -> Witness:
        return cls(word, word, ())

    def verify(self, r: Word) -> None:
        result = self.source
        for g, positive in self.factors:
            result = mul(result, conjugate(g, r if positive else inv(r)))
        if result != self.target:
            raise ValueError("normal-closure witness identity failed")

    def trans(self, other: Witness) -> Witness:
        if self.target != other.source:
            raise ValueError("witness endpoints do not match")
        return Witness(self.source, other.target, self.factors + other.factors)

    def conj(self, g: Word) -> Witness:
        return Witness(conjugate(g, self.source), conjugate(g, self.target),
                       tuple((mul(g, h), sign) for h, sign in self.factors))

    def inverse(self) -> Witness:
        return Witness(inv(self.source), inv(self.target),
                       tuple((mul(self.source, g), not sign)
                             for g, sign in reversed(self.factors)))

    def product(self, other: Witness) -> Witness:
        left = tuple((mul(inv(other.source), g), sign) for g, sign in self.factors)
        return Witness(mul(self.source, other.source), mul(self.target, other.target),
                       left + other.factors)

    def zpow(self, exponent: int) -> Witness:
        base = self if exponent >= 0 else self.inverse()
        result = Witness.refl(())
        for _ in range(abs(exponent)):
            result = result.product(base)
        return result


class Compiler:
    """Charge whole-word primitive constructors and expand conjugations to IDs."""

    def __init__(self, initial: tuple[Word, Word]):
        self.state = initial
        self.moves: list[int] = []
        self.proof_primitives = 0

    def emit(self, mid: int) -> None:
        self.moves.append(mid)
        self.state = tuple(map(tuple, raw.apply_move([list(w) for w in self.state], mid)))

    def invert(self, slot: int) -> None:
        self.proof_primitives += 1
        self.emit(slot)

    def multiply(self, slot: int) -> None:
        self.proof_primitives += 1
        self.emit(2 + 2 * slot)

    def conj(self, slot: int, g: Word) -> None:
        self.proof_primitives += 1
        for letter in reversed(g):
            self.emit(6 + 4 * slot + (1, -1, 2, -2).index(letter))

    def factor(self, slot: int, factor: Factor) -> None:
        source = 1 - slot
        original = self.state[source]
        g, positive = factor
        self.conj(source, g)
        if not positive:
            self.invert(source)
        self.multiply(slot)
        if not positive:
            self.invert(source)
        self.conj(source, inv(g))
        if self.state[source] != original:
            raise ValueError("factor compilation failed to restore the source relator")

    def zpow(self, slot: int, exponent: int) -> None:
        source = 1 - slot
        if exponent < 0:
            self.invert(source)
        for _ in range(abs(exponent)):
            self.multiply(slot)
        if exponent < 0:
            self.invert(source)

    def swap(self) -> None:
        original = self.state[0]
        self.multiply(0)
        self.invert(0)
        self.multiply(1)
        self.invert(0)
        self.conj(0, inv(original))
        self.multiply(0)
        self.invert(1)
