import ACSquareP3RootBridge

/-! Power substitutions retain a supplied list whose length grows with the exponent. -/

namespace AC.Substitution.PowerConjugacy
open AC.Certificate

variable {n : ℕ}

def root (a c : Word n) : Word n := c⁻¹ * a ^ 2 * c * a⁻¹

def doubleWitness (a c : Word n) :
    Witness (root a c) (c * a * c⁻¹) (a ^ 2) where
  factors := [(c * a⁻¹, true)]
  sound := by dsimp [root, product, Factor.value]; group

/-- The reverse power witness is available for every integer exponent. -/
def halve (a c : Word n) (e : ℤ) :
    Witness (root a c) (a ^ (2 * e)) (c * a ^ e * c⁻¹) :=
  ((doubleWitness a c).zpow e).reverse.change
    (by simp only [zpow_mul, zpow_ofNat]) (by rw [conj_zpow])

/-- The opposite orientation doubles a base power while conjugating it. -/
def expand (a c : Word n) (e : ℤ) :
    Witness (root a c) (a ^ e) (c⁻¹ * a ^ (2 * e) * c) :=
  (((doubleWitness a c).zpow e).conj c⁻¹).change
    (by rw [conj_zpow]; group)
    (by simp only [zpow_mul, zpow_ofNat]; group)

@[simp] theorem halve_length (a c : Word n) (e : ℤ) :
    (halve a c e).factors.length = e.natAbs := by
  simp [halve, doubleWitness]

@[simp] theorem expand_length (a c : Word n) (e : ℤ) :
    (expand a c e).factors.length = e.natAbs := by
  simp [expand, doubleWitness]

/-- A replacement inside arbitrary context leaves its donor relator in place. -/
theorem halve_in_context (R : Relators n) (i j : Fin n) (hij : i ≠ j)
    (a c before after : Word n) (e : ℤ)
    (hi : R i = before * a ^ (2 * e) * after)
    (hj : R j = root a c) :
    Steps R (cost ((halve a c e).factors))
      (Function.update R i (before * (c * a ^ e * c⁻¹) * after)) := by
  let w := ((Witness.refl (root a c) before).mul (halve a c e)).mul
    (Witness.refl (root a c) after)
  have hw : R i * product (R j) w.factors = before * (c * a ^ e * c⁻¹) * after := by
    simpa only [hi, hj] using w.sound
  have hc : cost w.factors = cost (halve a c e).factors := by
    simp [w, Witness.refl, cost]
  simpa only [hc] using replace R i j hij w.factors _ hw

end AC.Substitution.PowerConjugacy
