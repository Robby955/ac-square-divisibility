import ACMillerSchuppCriterion

/-!
# Counted endpoints for finite Miller–Schupp substitution witnesses

The counts use the official ordinary constructors, including arbitrary-word
conjugations. They are counts of the constructed paths, not minimal distances
or counts in the generator-only numbered action system.
-/

namespace AC.Certificate

/-- Exchange two relators using seven official ordinary constructors. -/
theorem Steps.swap {n : ℕ} (R : Relators n) (i j : Fin n) (hij : i ≠ j) :
    Steps R 7 (R ∘ Equiv.swap i j) := by
  let R₁ := Function.update R i (R i * R j)
  let R₂ := Function.update R₁ i (R₁ i)⁻¹
  let R₃ := Function.update R₂ j (R₂ j * R₂ i)
  let R₄ := Function.update R₃ i (R₃ i)⁻¹
  let R₅ := Function.update R₄ i ((R i)⁻¹ * R₄ i * ((R i)⁻¹)⁻¹)
  let R₆ := Function.update R₅ i (R₅ i * R₅ j)
  let R₇ := Function.update R₆ j (R₆ j)⁻¹
  have h₁ : Step R R₁ := .mulRight R i j hij
  have h₂ : Step R₁ R₂ := .inv R₁ i
  have h₃ : Step R₂ R₃ := .mulRight R₂ j i hij.symm
  have h₄ : Step R₃ R₄ := .inv R₃ i
  have h₅ : Step R₄ R₅ := .conj R₄ i (R i)⁻¹
  have h₆ : Step R₅ R₆ := .mulRight R₅ i j hij
  have h₇ : Step R₆ R₇ := .inv R₆ j
  have end_eq : R₇ = R ∘ Equiv.swap i j := by
    ext k
    by_cases hki : k = i
    · subst k
      simp [R₇, R₆, R₅, R₄, R₃, R₂, R₁, hij, hij.symm, mul_assoc]
    · by_cases hkj : k = j
      · subst k
        simp [R₇, R₆, R₅, R₄, R₃, R₂, R₁, hij, hij.symm, mul_assoc]
      · simp [R₇, R₆, R₅, R₄, R₃, R₂, R₁, hki, hkj,
              Equiv.swap_apply_of_ne_of_ne hki hkj]
  rw [← end_eq]
  exact ((((((Steps.single h₁).tail h₂).tail h₃).tail h₄).tail h₅).tail h₆).tail h₇

end AC.Certificate

namespace AC.MillerSchupp

open AC.Certificate AC.WordTransport

/-- The two-factor elimination and elementary endpoint have an exact move count. -/
theorem power_second_steps (n : ℕ) (b : ℤ) :
    Steps (pair (first n) (x⁻¹ * y ^ b))
      (b.natAbs + (if 0 < b then 2 else 0) + 17) (standard 2) := by
  have h₁ : Steps (pair (first n) (x⁻¹ * y ^ b)) 8
      (pair y⁻¹ (x⁻¹ * y ^ b)) := by
    have h := Substitution.replace (pair (first n) (x⁻¹ * y ^ b)) 0 1 (by decide)
      [(y ^ (n + 1 : ℤ), true), (y, false)] y⁻¹ (by
        simpa only [pair_zero, pair_one] using power_elimination_witness n b)
    simpa only [pair_update_zero, Substitution.cost, Substitution.Factor.cost] using h
  have h₂ : Steps (pair y⁻¹ (x⁻¹ * y ^ b)) 1 (pair y (x⁻¹ * y ^ b)) := by
    simpa only [pair_zero, inv_inv, pair_update_zero] using
      Steps.single (Step.inv (pair y⁻¹ (x⁻¹ * y ^ b)) 0)
  have h₃ : Steps (pair y (x⁻¹ * y ^ b))
      (b.natAbs + if 0 < b then 2 else 0) (pair y x⁻¹) := by
    have h := mulRight_zpow (pair y (x⁻¹ * y ^ b)) 1 0 (by decide) (-b)
    simpa [mul_assoc] using h
  have h₄ : Steps (pair y x⁻¹) 1 (pair y x) := by
    simpa only [pair_one, inv_inv, pair_update_one] using
      Steps.single (Step.inv (pair y x⁻¹) 1)
  have he : pair y x ∘ Equiv.swap (0 : Fin 2) 1 = standard 2 := by
    ext i
    fin_cases i <;> simp [pair, standard, x, y]
  have h₅ : Steps (pair y x) 7 (standard 2) := by
    simpa only [he] using Steps.swap (pair y x) 0 1 (by decide)
  convert h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅))) using 1
  omega

theorem power_second_counted (n : ℕ) (b : ℤ) :
    ∃ l ≤ b.natAbs + 19,
      Steps (pair (first n) (x⁻¹ * y ^ b)) l (standard 2) := by
  refine ⟨_, ?_, power_second_steps n b⟩
  split_ifs <;> omega

/-- Conjugation of the second relator adds exactly one official constructor. -/
theorem power_conjugate_second_steps (n : ℕ) (a b : ℤ) :
    Steps (pair (first n) (x⁻¹ * (x ^ a * y ^ b * x ^ (-a))))
      (b.natAbs + (if 0 < b then 2 else 0) + 18) (standard 2) := by
  have he : x ^ (-a) * (x⁻¹ * (x ^ a * y ^ b * x ^ (-a))) * (x ^ (-a))⁻¹ =
      x⁻¹ * y ^ b := by group
  have h : Step (pair (first n) (x⁻¹ * (x ^ a * y ^ b * x ^ (-a))))
      (pair (first n) (x⁻¹ * y ^ b)) := by
    simpa only [pair_one, he, pair_update_one] using
      Step.conj (pair (first n) (x⁻¹ * (x ^ a * y ^ b * x ^ (-a)))) 1 (x ^ (-a))
  convert (Steps.single h).trans (power_second_steps n b) using 1
  omega

theorem power_conjugate_second_counted (n : ℕ) (a b : ℤ) :
    ∃ l ≤ b.natAbs + 20,
      Steps (pair (first n) (x⁻¹ * (x ^ a * y ^ b * x ^ (-a)))) l (standard 2) := by
  refine ⟨_, ?_, power_conjugate_second_steps n a b⟩
  split_ifs <;> omega

/-- The finite witness cost is added to the exact conjugated-power endpoint count. -/
theorem witnessed_power_conjugate_steps (n : ℕ) (a b : ℤ) (w : Word 2)
    (fs : List (Substitution.Factor 2))
    (witness : (x⁻¹ * w) * Substitution.product (first n) fs =
      x⁻¹ * (x ^ a * y ^ b * x ^ (-a))) :
    Steps (pair (first n) (x⁻¹ * w))
      (Substitution.cost fs + b.natAbs + (if 0 < b then 2 else 0) + 18)
      (standard 2) := by
  have h := Substitution.replace (pair (first n) (x⁻¹ * w)) 1 0 (by decide) fs
    (x⁻¹ * (x ^ a * y ^ b * x ^ (-a))) (by
      simpa only [pair_zero, pair_one] using witness)
  have hp : Steps (pair (first n) (x⁻¹ * w)) (Substitution.cost fs)
      (pair (first n) (x⁻¹ * (x ^ a * y ^ b * x ^ (-a)))) := by
    simpa only [pair_update_one] using h
  convert hp.trans (power_conjugate_second_steps n a b) using 1
  omega

theorem witnessed_power_conjugate_counted (n : ℕ) (a b : ℤ) (w : Word 2)
    (fs : List (Substitution.Factor 2))
    (witness : (x⁻¹ * w) * Substitution.product (first n) fs =
      x⁻¹ * (x ^ a * y ^ b * x ^ (-a))) :
    ∃ l ≤ Substitution.cost fs + b.natAbs + 20,
      Steps (pair (first n) (x⁻¹ * w)) l (standard 2) := by
  refine ⟨_, ?_, witnessed_power_conjugate_steps n a b w fs witness⟩
  split_ifs <;> omega

/-- Exact count for the dataset convention, including its two conversion moves. -/
theorem witnessed_power_conjugate_metadata_steps (n : ℕ) (a b : ℤ) (w : Word 2)
    (fs : List (Substitution.Factor 2))
    (witness : (x⁻¹ * w) * Substitution.product (first n) fs =
      x⁻¹ * (x ^ a * y ^ b * x ^ (-a))) :
    Steps (pair (first n) (x * w⁻¹))
      (Substitution.cost fs + b.natAbs + (if 0 < b then 2 else 0) + 20)
      (standard 2) := by
  convert (metadata_to_second_steps n w).trans
    (witnessed_power_conjugate_steps n a b w fs witness) using 1
  omega

theorem witnessed_power_conjugate_metadata_counted (n : ℕ) (a b : ℤ) (w : Word 2)
    (fs : List (Substitution.Factor 2))
    (witness : (x⁻¹ * w) * Substitution.product (first n) fs =
      x⁻¹ * (x ^ a * y ^ b * x ^ (-a))) :
    ∃ l ≤ Substitution.cost fs + b.natAbs + 22,
      Steps (pair (first n) (x * w⁻¹)) l (standard 2) := by
  refine ⟨_, ?_, witnessed_power_conjugate_metadata_steps n a b w fs witness⟩
  split_ifs <;> omega

end AC.MillerSchupp
