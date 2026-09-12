import ACPowerConjugacy

/-! Counted halving paths expose the companion shift that an induction must restore. -/

namespace AC.MillerSchupp.SquareFamily.Residual
open AC.Certificate AC.Substitution

def halvingCost (p d : ℤ) : ℕ :=
  cost (PowerConjugacy.halve x (y ^ p) (-d)).factors + 1

/-- Halving alone changes the residual remainder by the root degree. -/
theorem halve_shift (p r d : ℤ) :
    Steps (pair (P2.root p) (relation r (2 * d))) (halvingCost p d)
      (pair (P2.root p) (relation (r + p) d)) := by
  let before := y ^ (-(r + 1)) * x⁻¹ * y ^ r
  have hi : pair (P2.root p) (relation r (2 * d)) 1 =
      before * x ^ (2 * (-d)) * 1 := by dsimp [before, relation, pair]; group
  have hj : pair (P2.root p) (relation r (2 * d)) 0 =
      PowerConjugacy.root x (y ^ p) := by
    simp [PowerConjugacy.root, P2.root, zpow_neg]
  have h₁ := PowerConjugacy.halve_in_context
    (pair (P2.root p) (relation r (2 * d))) 1 0 (by decide)
    x (y ^ p) before 1 (-d) hi hj
  simp only [mul_one, pair_update_one] at h₁
  have h₂ := Steps.single (Step.conj
    (pair (P2.root p) (before * (y ^ p * x ^ (-d) * (y ^ p)⁻¹))) 1 (y ^ (-p)))
  have he : y ^ (-p) * (before * (y ^ p * x ^ (-d) * (y ^ p)⁻¹)) *
      (y ^ (-p))⁻¹ = relation (r + p) d := by dsimp [before, relation]; group
  simp only [pair_one, he, pair_update_one] at h₂
  exact h₁.trans h₂

/-- The changed degree-two companion is indexed by its outer stable-letter shift. -/
def shiftedCompanion (r d : ℤ) : Word 2 :=
  y ^ (-(r + 1)) * x⁻¹ * y⁻¹ * x⁻¹ * y ^ (r + 1) * x ^ (-d)

@[simp] theorem shiftedCompanion_zero (d : ℤ) :
    shiftedCompanion 0 d = twoRootCompanion d := by
  simp [shiftedCompanion, twoRootCompanion]

/-- In the degree-two coordinates, halving shifts the outer exponent by two. -/
theorem two_root_halve_shift (r d : ℤ) :
    Steps (pair (P2.root 2) (shiftedCompanion r (2 * d))) (halvingCost 2 d)
      (pair (P2.root 2) (shiftedCompanion (r + 2) d)) := by
  let before := y ^ (-(r + 1)) * x⁻¹ * y⁻¹ * x⁻¹ * y ^ (r + 1)
  have hi : pair (P2.root 2) (shiftedCompanion r (2 * d)) 1 =
      before * x ^ (2 * (-d)) * 1 := by dsimp [before, shiftedCompanion, pair]; group
  have hj : pair (P2.root 2) (shiftedCompanion r (2 * d)) 0 =
      PowerConjugacy.root x (y ^ (2 : ℤ)) := by
    simp [PowerConjugacy.root, P2.root, zpow_neg]
  have h₁ := PowerConjugacy.halve_in_context
    (pair (P2.root 2) (shiftedCompanion r (2 * d))) 1 0 (by decide)
    x (y ^ (2 : ℤ)) before 1 (-d) hi hj
  simp only [mul_one, pair_update_one] at h₁
  have h₂ := Steps.single (Step.conj
    (pair (P2.root 2) (before * (y ^ (2 : ℤ) * x ^ (-d) * (y ^ (2 : ℤ))⁻¹)))
    1 (y ^ (-2 : ℤ)))
  have he : y ^ (-2 : ℤ) * (before * (y ^ (2 : ℤ) * x ^ (-d) * (y ^ (2 : ℤ))⁻¹)) *
      (y ^ (-2 : ℤ))⁻¹ = shiftedCompanion (r + 2) d := by
    dsimp [before, shiftedCompanion]; group
  simp only [pair_one, he, pair_update_one] at h₂
  exact h₁.trans h₂

/-- This uniform bound counts arbitrary-word conjugations as single primitives. -/
theorem halvingCost_bounds (p d : ℤ) :
    3 * d.natAbs + 1 ≤ halvingCost p d ∧ halvingCost p d ≤ 5 * d.natAbs + 1 := by
  have h := cost_bounds (PowerConjugacy.halve x (y ^ p) (-d)).factors
  simp only [PowerConjugacy.halve_length, Int.natAbs_neg] at h
  dsimp [halvingCost]
  omega

/-- The missing restoration is an explicit hypothesis, required only at even
powers of two; the already supplied d=1 and d=2 seeds start the induction. -/
theorem degree_three_of_restoration
    (restore : ∀ j : ℕ,
      Reachable (pair (P2.root 2) (shiftedCompanion 2 ((2 : ℤ) ^ (j + 1))))
        (pair (P2.root 2) (twoRootCompanion ((2 : ℤ) ^ (j + 1)))))
    (m : ℕ) : Reachable (Diagonal.generalSquare 3 (3 * m + 1)) (standard 2) := by
  apply (degree_three_two_root_iff m).mpr
  cases m with
  | zero =>
    simpa using (root_three_two_iff 1).mp degree_three_base
  | succ n =>
    induction n with
    | zero =>
      simpa using (root_three_two_iff 2).mp seed_one_steps.reachable
    | succ n ih =>
      have half := (two_root_halve_shift 0 ((2 : ℤ) ^ (n + 1))).reachable
      simp only [shiftedCompanion_zero, zero_add] at half
      have step := half.trans ((restore n).trans ih)
      simpa only [pow_succ, mul_comm, Nat.succ_eq_add_one] using step

/-- Restoration at these exponents is equivalent to the target family theorem.
This supplies neither side of the equivalence without an additional proof. -/
theorem degree_three_all_iff_restoration :
    (∀ m : ℕ, Reachable (Diagonal.generalSquare 3 (3 * m + 1)) (standard 2)) ↔
    (∀ j : ℕ,
      Reachable (pair (P2.root 2) (shiftedCompanion 2 ((2 : ℤ) ^ (j + 1))))
        (pair (P2.root 2) (twoRootCompanion ((2 : ℤ) ^ (j + 1))))) := by
  constructor
  · intro solved j
    have hi := (degree_three_two_root_iff (j + 2)).mp (solved (j + 2))
    have lo := (degree_three_two_root_iff (j + 1)).mp (solved (j + 1))
    have half := (two_root_halve_shift 0 ((2 : ℤ) ^ (j + 1))).reachable
    simp only [shiftedCompanion_zero, zero_add] at half
    have hi' : Reachable
        (pair (P2.root 2) (twoRootCompanion (2 * (2 : ℤ) ^ (j + 1))))
        (standard 2) := by
      simpa only [show j + 2 = (j + 1) + 1 by omega, pow_succ, mul_comm] using hi
    exact (ResidueClasses.reverse_path half).trans
      (hi'.trans (ResidueClasses.reverse_path lo))
  · exact degree_three_of_restoration

end AC.MillerSchupp.SquareFamily.Residual
