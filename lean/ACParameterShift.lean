import ACDivisibility

/-!
# Counted transport along Miller–Schupp parameter shifts

The Baumslag–Solitar relation is used through explicit signed normal-closure
witnesses. The first relator is restored after every factor. The costs count
official arbitrary-word conjugation constructors and are not minimal distances.
This formalizes an algebraic orbit relation; mathematical novelty is unassessed.
-/

namespace AC.MillerSchupp.ParameterShift

open AC.Certificate AC.Substitution

/-- Positive shifts use negative factors; negative shifts use positive factors. -/
def shiftCost (t : ℤ) : ℕ := (if t < 0 then 3 else 5) * t.natAbs

theorem riseOne_cost (n : ℕ) (t : ℤ) :
    cost (Divisibility.riseOne n t).factors = shiftCost t := by
  cases t with
  | ofNat t =>
    have ht : ¬ (t : ℤ) < 0 := by omega
    simp [Divisibility.riseOne, Witness.zpow, Divisibility.riseBase,
      shiftCost, cost, Factor.cost, ht, Nat.mul_comm]
  | negSucc t =>
    have h := Witness.cost_inverse ((Divisibility.riseBase n).pow (t + 1))
    have hc : cost (Divisibility.riseBase n).factors = 5 := rfl
    have hl : (Divisibility.riseBase n).factors.length = 1 := rfl
    simp only [Witness.cost_pow, Witness.length_pow, hc, hl, mul_one] at h
    change cost ((Divisibility.riseBase n).pow (t + 1)).inverse.factors =
      shiftCost (Int.negSucc t)
    simp only [shiftCost, Int.negSucc_lt_zero, ↓reduceIte, Int.natAbs_negSucc]
    omega

theorem shiftCost_bound (t : ℤ) : shiftCost t ≤ 5 * t.natAbs := by
  unfold shiftCost
  split_ifs <;> omega

/-- An explicit ambient free-group witness for one integer parameter shift. -/
def shiftWitness (n : ℕ) (a b c t : ℤ) :
    Witness (first n) (second a b c)
      (second (a - (n : ℤ) * t) (b + (n + 1 : ℤ) * t) c) :=
  (((Witness.refl (first n) (x⁻¹ * y ^ (a - (n : ℤ) * t))).mul
    (Divisibility.riseOne n t)).mul
      (Witness.refl (first n) (x * y ^ b * x⁻¹ * y ^ c))).change
        (by unfold second; group) (by unfold second; group)

@[simp] theorem shiftWitness_length (n : ℕ) (a b c t : ℤ) :
    (shiftWitness n a b c t).factors.length = t.natAbs := by
  simp [shiftWitness]

@[simp] theorem shiftWitness_cost (n : ℕ) (a b c t : ℤ) :
    cost (shiftWitness n a b c t).factors = shiftCost t := by
  simp [shiftWitness, Witness.refl, cost, riseOne_cost]

/-- Compile the entire signed witness, with the first relator restored. -/
theorem shift_steps (n : ℕ) (a b c t : ℤ) :
    Steps (presentation n a b c) (shiftCost t)
      (presentation n (a - (n : ℤ) * t) (b + (n + 1 : ℤ) * t) c) := by
  have h := Substitution.replace (presentation n a b c) 1 0 (by decide)
    (shiftWitness n a b c t).factors
    (second (a - (n : ℤ) * t) (b + (n + 1 : ℤ) * t) c) (by
      simpa [presentation] using (shiftWitness n a b c t).sound)
  simpa [presentation] using h

/-- Pull a supplied solution across a shift using its explicit reverse witness. -/
theorem shift_solution_steps (n : ℕ) (a b c t : ℤ) {L : ℕ}
    (h : Steps (presentation n a b c) L (standard 2)) :
    Steps (presentation n (a - (n : ℤ) * t) (b + (n + 1 : ℤ) * t) c)
      (shiftCost (-t) + L) (standard 2) := by
  have hs := shift_steps n (a - (n : ℤ) * t) (b + (n + 1 : ℤ) * t) c (-t)
  have ha : a - (n : ℤ) * t - (n : ℤ) * (-t) = a := by ring
  have hb : b + (n + 1 : ℤ) * t + (n + 1 : ℤ) * (-t) = b := by ring
  rw [ha, hb] at hs
  exact hs.trans h

theorem shift_solution_counted (n : ℕ) (a b c t : ℤ) {L : ℕ}
    (h : Steps (presentation n a b c) L (standard 2)) :
    ∃ l ≤ L + 5 * t.natAbs,
      Steps (presentation n (a - (n : ℤ) * t) (b + (n + 1 : ℤ) * t) c)
        l (standard 2) := by
  have hb := shiftCost_bound (-t)
  simp only [Int.natAbs_neg] at hb
  exact ⟨_, by omega, shift_solution_steps n a b c t h⟩

/-- Solvability is constant along the complete integer parameter-shift orbit. -/
theorem shift_solvable_iff (n : ℕ) (a b c t : ℤ) :
    Reachable (presentation n a b c) (standard 2) ↔
      Reachable (presentation n (a - (n : ℤ) * t) (b + (n + 1 : ℤ) * t) c)
        (standard 2) := by
  constructor
  · intro h
    have hs := shift_steps n (a - (n : ℤ) * t) (b + (n + 1 : ℤ) * t) c (-t)
    have ha : a - (n : ℤ) * t - (n : ℤ) * (-t) = a := by ring
    have hb : b + (n + 1 : ℤ) * t + (n + 1 : ℤ) * (-t) = b := by ring
    rw [ha, hb] at hs
    exact hs.reachable.trans h
  · intro h
    exact (shift_steps n a b c t).reachable.trans h

/-- A supplied seed transports along the shift and arbitrary final-exponent shear. -/
theorem shift_shear_solution_counted (n : ℕ) (a b c t c' : ℤ) {L : ℕ}
    (h : Steps (presentation n a b c) L (standard 2)) :
    ∃ l ≤ L + 5 * t.natAbs + (c - c').natAbs + 3,
      Steps (presentation n (a - (n : ℤ) * t) (b + (n + 1 : ℤ) * t) c')
        l (standard 2) := by
  obtain ⟨l, hb, hs⟩ := shift_solution_counted n a b c t h
  obtain ⟨k, hk, hfinal⟩ := shear_family_counted n
    (a - (n : ℤ) * t) (b + (n + 1 : ℤ) * t) c hs c'
  exact ⟨k, by omega, hfinal⟩

/-- The existing shear proof and explicit shift witness give a two-parameter orbit. -/
theorem shift_shear_solvable_iff (n : ℕ) (a b c t c' : ℤ) :
    Reachable (presentation n a b c) (standard 2) ↔
      Reachable (presentation n (a - (n : ℤ) * t) (b + (n + 1 : ℤ) * t) c')
        (standard 2) := by
  constructor
  · intro h
    exact shear_family n (a - (n : ℤ) * t) (b + (n + 1 : ℤ) * t) c
      ((shift_solvable_iff n a b c t).mp h) c'
  · intro h
    exact (shift_solvable_iff n a b c t).mpr
      (shear_family n (a - (n : ℤ) * t) (b + (n + 1 : ℤ) * t) c' h c)

/-- A complete invariant of the explicit integer shift on the two exponents. -/
def invariant (n : ℕ) (a b : ℤ) : ℤ := (n + 1 : ℤ) * a + (n : ℤ) * b

theorem invariant_shift (n : ℕ) (a b t : ℤ) :
    invariant n (a - (n : ℤ) * t) (b + (n + 1 : ℤ) * t) = invariant n a b := by
  unfold invariant
  ring

/-- Equal invariants determine the shift explicitly; no division is needed. -/
theorem parameters_of_invariant (n : ℕ) (a b a' b' : ℤ)
    (h : invariant n a b = invariant n a' b') :
    a - (n : ℤ) * (a' + b' - a - b) = a' ∧
      b + (n + 1 : ℤ) * (a' + b' - a - b) = b' := by
  unfold invariant at h
  constructor <;> nlinarith

/-- Equal invariant and fixed final exponent yield an actual counted AC path. -/
theorem same_invariant_steps (n : ℕ) (a b a' b' c : ℤ)
    (h : invariant n a b = invariant n a' b') :
    Steps (presentation n a b c) (shiftCost (a' + b' - a - b))
      (presentation n a' b' c) := by
  obtain ⟨ha, hb⟩ := parameters_of_invariant n a b a' b' h
  simpa only [ha, hb] using shift_steps n a b c (a' + b' - a - b)

/-- Equal invariant allows solution transport even when the final exponent changes. -/
theorem same_invariant_solution_counted (n : ℕ) (a b c a' b' c' : ℤ)
    (he : invariant n a b = invariant n a' b') {L : ℕ}
    (h : Steps (presentation n a b c) L (standard 2)) :
    ∃ l ≤ L + 5 * (a' + b' - a - b).natAbs + (c - c').natAbs + 3,
      Steps (presentation n a' b' c') l (standard 2) := by
  obtain ⟨ha, hb⟩ := parameters_of_invariant n a b a' b' he
  simpa only [ha, hb] using
    shift_shear_solution_counted n a b c (a' + b' - a - b) c' h

theorem same_invariant_solvable_iff (n : ℕ) (a b c a' b' c' : ℤ)
    (h : invariant n a b = invariant n a' b') :
    Reachable (presentation n a b c) (standard 2) ↔
      Reachable (presentation n a' b' c') (standard 2) := by
  obtain ⟨ha, hb⟩ := parameters_of_invariant n a b a' b' h
  simpa only [ha, hb] using
    shift_shear_solvable_iff n a b c (a' + b' - a - b) c'

/-- A prescribed representative for the proven shift-and-shear solution orbit. -/
theorem canonical_solvable_iff (n : ℕ) (a b c : ℤ) :
    Reachable (presentation n a b c) (standard 2) ↔
      Reachable (presentation n (invariant n a b) (-invariant n a b) 0)
        (standard 2) :=
  same_invariant_solvable_iff n a b c (invariant n a b) (-invariant n a b) 0
    (by unfold invariant; ring)

theorem canonical_solution_counted (n : ℕ) (a b c : ℤ) {L : ℕ}
    (h : Steps (presentation n a b c) L (standard 2)) :
    ∃ l ≤ L + 5 * (a + b).natAbs + c.natAbs + 3,
      Steps (presentation n (invariant n a b) (-invariant n a b) 0)
        l (standard 2) := by
  have ha : a - (n : ℤ) * (-(a + b)) = invariant n a b := by unfold invariant; ring
  have hb : b + (n + 1 : ℤ) * (-(a + b)) = -invariant n a b := by unfold invariant; ring
  simpa only [ha, hb, Int.natAbs_neg, sub_zero] using
    shift_shear_solution_counted n a b c (-(a + b)) 0 h

end AC.MillerSchupp.ParameterShift
