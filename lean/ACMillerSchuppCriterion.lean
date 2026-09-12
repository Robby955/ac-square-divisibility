import ACMillerSchupp
import ACSubstitution

/-!
# A witnessed power-conjugate criterion for Miller–Schupp presentations

The input is an exact identity in the ambient free group, expressed as a finite
product of conjugates of the first relator. Every use of that identity is
compiled to official ordinary moves with the other relator restored.
-/

namespace AC.MillerSchupp

open AC.Certificate AC.WordTransport

@[simp] theorem pair_zero (r q : Word 2) : pair r q 0 = r := rfl
@[simp] theorem pair_one (r q : Word 2) : pair r q 1 = q := rfl

@[simp] theorem pair_update_zero (r q z : Word 2) :
    Function.update (pair r q) 0 z = pair z q := by
  ext i
  fin_cases i <;> simp [pair]

@[simp] theorem pair_update_one (r q z : Word 2) :
    Function.update (pair r q) 1 z = pair r z := by
  ext i
  fin_cases i <;> simp [pair]

/-- Two explicit factors replace the Baumslag–Solitar relator by `y⁻¹`. -/
theorem power_elimination_witness (n : ℕ) (b : ℤ) :
    first n * Substitution.product (x⁻¹ * y ^ b)
      [(y ^ (n + 1 : ℤ), true), (y, false)] = y⁻¹ := by
  change first n * ((y ^ (n + 1 : ℤ) * (x⁻¹ * y ^ b) * (y ^ (n + 1 : ℤ))⁻¹) *
    ((y * (x⁻¹ * y ^ b)⁻¹ * y⁻¹) * 1)) = y⁻¹
  unfold first
  group

/-- Once the second relator is `x⁻¹ y^b`, the presentation is ordinarily solvable. -/
theorem power_second_solvable (n : ℕ) (b : ℤ) :
    Reachable (pair (first n) (x⁻¹ * y ^ b)) (standard 2) := by
  have h₁ : Reachable (pair (first n) (x⁻¹ * y ^ b))
      (pair y⁻¹ (x⁻¹ * y ^ b)) := by
    have h := Substitution.replace (pair (first n) (x⁻¹ * y ^ b)) 0 1 (by decide)
      [(y ^ (n + 1 : ℤ), true), (y, false)] y⁻¹ (by
        simpa only [pair_zero, pair_one] using power_elimination_witness n b)
    simpa only [pair_update_zero] using h.reachable
  have h₂ : Reachable (pair y⁻¹ (x⁻¹ * y ^ b)) (pair y (x⁻¹ * y ^ b)) := by
    simpa only [pair_zero, inv_inv, pair_update_zero] using
      Reachable.single (Step.inv (pair y⁻¹ (x⁻¹ * y ^ b)) 0)
  have h₃ : Reachable (pair y (x⁻¹ * y ^ b)) (pair y x⁻¹) := by
    have h := mulRight_zpow (pair y (x⁻¹ * y ^ b)) 1 0 (by decide) (-b)
    simpa [mul_assoc] using h.reachable
  have h₄ : Reachable (pair y x⁻¹) (pair y x) := by
    simpa only [pair_one, inv_inv, pair_update_one] using
      Reachable.single (Step.inv (pair y x⁻¹) 1)
  have he : pair y x ∘ Equiv.swap (0 : Fin 2) 1 = standard 2 := by
    ext i
    fin_cases i <;> simp [pair, standard, x, y]
  have h₅ : Reachable (pair y x) (standard 2) := by
    simpa only [he] using Reachable.swap (pair y x) 0 1 (by decide)
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

/-- A conjugated power on the complete right-hand side is a solved family. -/
theorem power_conjugate_second_solvable (n : ℕ) (a b : ℤ) :
    Reachable (pair (first n) (x⁻¹ * (x ^ a * y ^ b * x ^ (-a)))) (standard 2) := by
  have he : x ^ (-a) * (x⁻¹ * (x ^ a * y ^ b * x ^ (-a))) * (x ^ (-a))⁻¹ =
      x⁻¹ * y ^ b := by group
  have h : Step (pair (first n) (x⁻¹ * (x ^ a * y ^ b * x ^ (-a))))
      (pair (first n) (x⁻¹ * y ^ b)) := by
    simpa only [pair_one, he, pair_update_one] using
      Step.conj (pair (first n) (x⁻¹ * (x ^ a * y ^ b * x ^ (-a)))) 1 (x ^ (-a))
  exact (Reachable.single h).trans (power_second_solvable n b)

/-- A finite witnessed substitution suffices uniformly in `n`, `a`, `b` and `w`. -/
theorem witnessed_power_conjugate_solvable (n : ℕ) (a b : ℤ) (w : Word 2)
    (fs : List (Substitution.Factor 2))
    (witness : (x⁻¹ * w) * Substitution.product (first n) fs =
      x⁻¹ * (x ^ a * y ^ b * x ^ (-a))) :
    Reachable (pair (first n) (x⁻¹ * w)) (standard 2) := by
  have h := Substitution.replace (pair (first n) (x⁻¹ * w)) 1 0 (by decide) fs
    (x⁻¹ * (x ^ a * y ^ b * x ^ (-a))) (by
      simpa only [pair_zero, pair_one] using witness)
  have hp : Reachable (pair (first n) (x⁻¹ * w))
      (pair (first n) (x⁻¹ * (x ^ a * y ^ b * x ^ (-a)))) := by
    simpa only [pair_update_one] using h.reachable
  exact hp.trans (power_conjugate_second_solvable n a b)

/-- Official metadata uses `x w⁻¹`; the convenient convention costs two moves. -/
theorem metadata_to_second_steps (n : ℕ) (w : Word 2) :
    Steps (pair (first n) (x * w⁻¹)) 2 (pair (first n) (x⁻¹ * w)) := by
  have h₁ : Step (pair (first n) (x * w⁻¹)) (pair (first n) (w⁻¹ * x)) := by
    simpa [mul_assoc] using Step.conj (pair (first n) (x * w⁻¹)) 1 x⁻¹
  have h₂ : Step (pair (first n) (w⁻¹ * x)) (pair (first n) (x⁻¹ * w)) := by
    simpa using Step.inv (pair (first n) (w⁻¹ * x)) 1
  exact (Steps.single h₁).tail h₂

/-- The witnessed criterion for the exact second-relator convention in the dataset. -/
theorem witnessed_power_conjugate_metadata_solvable (n : ℕ) (a b : ℤ) (w : Word 2)
    (fs : List (Substitution.Factor 2))
    (witness : (x⁻¹ * w) * Substitution.product (first n) fs =
      x⁻¹ * (x ^ a * y ^ b * x ^ (-a))) :
    Reachable (pair (first n) (x * w⁻¹)) (standard 2) :=
  (metadata_to_second_steps n w).reachable.trans
    (witnessed_power_conjugate_solvable n a b w fs witness)

end AC.MillerSchupp
