import ACUniformShearFamily
import ACParameterShift
import ACYInversion

/-!
# Finite parameter residues for Miller–Schupp ordinary solvability

Every reverse move below is derived from the official constructors. Parameter
periods preserve existence of an ordinary solution; the generator shears used
to establish them are whole-path transports with proved standard endpoints.
No classification of full AC orbits, shortest paths, or novelty is asserted.
-/

namespace AC.MillerSchupp.ResidueClasses

open AC.Certificate

/-- Undo one official move using a finite path of official moves. -/
theorem reverse_step {n : ℕ} {R S : Relators n} (h : Step R S) : Reachable S R := by
  cases h with
  | inv i =>
    simpa using (Steps.single (Step.inv (Function.update R i (R i)⁻¹) i)).reachable
  | mulRight i j hij =>
    simpa [hij.symm, mul_assoc] using
      (Steps.mulInvRight (Function.update R i (R i * R j)) i j hij).reachable
  | conj i w =>
    simpa [mul_assoc] using
      (Steps.single (Step.conj (Function.update R i (w * R i * w⁻¹)) i w⁻¹)).reachable

theorem reverse_path {n : ℕ} {R S : Relators n} (h : Reachable R S) : Reachable S R := by
  induction h with
  | refl => exact .refl _
  | tail _ step ih => exact (reverse_step step).trans ih

theorem path_solvable_iff {n : ℕ} {R S : Relators n} (h : Reachable R S) :
    Reachable R (standard n) ↔ Reachable S (standard n) :=
  ⟨fun hr => (reverse_path h).trans hr, fun hs => h.trans hs⟩

theorem shear_solvable_iff (n : ℕ) (a b c c' : ℤ) :
    Reachable (presentation n a b c) (standard 2) ↔
      Reachable (presentation n a b c') (standard 2) :=
  ⟨fun h => shear_family n a b c h c', fun h => shear_family n a b c' h c⟩

/-- The four-move bridge and shear make `n` a period of the first exponent. -/
theorem a_period_one (n : ℕ) (a b c c' : ℤ) :
    Reachable (presentation n a b c) (standard 2) ↔
      Reachable (presentation n (a - (n : ℤ)) b c') (standard 2) :=
  (shear_solvable_iff n a b c (-(n + 1 : ℤ))).trans
    ((path_solvable_iff (Uniform.period_bridge_steps n a b).reachable).trans
      (shear_solvable_iff n (a - (n : ℤ)) b 0 c'))

/-- Iterate the first-parameter period in both integer directions. -/
theorem a_period (n : ℕ) (a b c t : ℤ) :
    Reachable (presentation n a b c) (standard 2) ↔
      Reachable (presentation n (a - (n : ℤ) * t) b c) (standard 2) := by
  induction t using Int.induction_on with
  | zero => simp
  | succ t ih =>
    have h := ih.trans (a_period_one n (a - (n : ℤ) * (t : ℤ)) b c c)
    have he : a - (n : ℤ) * (t : ℤ) - (n : ℤ) =
        a - (n : ℤ) * ((t : ℤ) + 1) := by ring
    simpa only [he] using h
  | pred t ih =>
    have hs := a_period_one n (a - (n : ℤ) * (-(t : ℤ) - 1)) b c c
    have he : a - (n : ℤ) * (-(t : ℤ) - 1) - (n : ℤ) =
        a - (n : ℤ) * (-(t : ℤ)) := by ring
    rw [he] at hs
    exact ih.trans hs.symm

/-- Combine the coupled parameter shift with the independent first-parameter period. -/
theorem b_period (n : ℕ) (a b c t : ℤ) :
    Reachable (presentation n a b c) (standard 2) ↔
      Reachable (presentation n a (b + (n + 1 : ℤ) * t) c) (standard 2) :=
  (ParameterShift.shift_solvable_iff n a b c t).trans
    (a_period n a (b + (n + 1 : ℤ) * t) c t).symm

/-- A prescribed residue representative; the equivalence also holds at `n=0`. -/
theorem residue_solvable_iff (n : ℕ) (a b c : ℤ) :
    Reachable (presentation n a b c) (standard 2) ↔
      Reachable (presentation n (a % (n : ℤ)) (b % (n + 1 : ℤ)) 0)
        (standard 2) := by
  have ha : a - (n : ℤ) * (a / (n : ℤ)) = a % (n : ℤ) :=
    (Int.emod_def a (n : ℤ)).symm
  have hb : b + (n + 1 : ℤ) * (-(b / (n + 1 : ℤ))) = b % (n + 1 : ℤ) := by
    rw [Int.emod_def]
    ring
  have h₁ := a_period n a b c (a / (n : ℤ))
  rw [ha] at h₁
  have h₂ := b_period n (a % (n : ℤ)) b c (-(b / (n + 1 : ℤ)))
  rw [hb] at h₂
  exact h₁.trans (h₂.trans (shear_solvable_iff n (a % (n : ℤ)) (b % (n + 1 : ℤ)) c 0))

/-- For positive `n`, the preceding theorem reduces every input to a finite grid. -/
theorem finite_residue_reduction (n : ℕ) (hn : 0 < n) (a b c : ℤ) :
    ∃ a' b' : ℤ, 0 ≤ a' ∧ a' < (n : ℤ) ∧ 0 ≤ b' ∧ b' < (n + 1 : ℤ) ∧
      (Reachable (presentation n a b c) (standard 2) ↔
        Reachable (presentation n a' b' 0) (standard 2)) := by
  have hn' : (n : ℤ) ≠ 0 := by omega
  have hn1 : (n + 1 : ℤ) ≠ 0 := by omega
  refine ⟨a % (n : ℤ), b % (n + 1 : ℤ), Int.emod_nonneg a hn', ?_,
    Int.emod_nonneg b hn1, ?_, residue_solvable_iff n a b c⟩
  · simpa using Int.emod_lt a hn'
  · simpa using Int.emod_lt b hn1

/-- With first exponent zero, one conjugation enters the power endpoint. -/
theorem zero_a_solvable (n : ℕ) (b c : ℤ) :
    Reachable (presentation n 0 b c) (standard 2) := by
  have he : y ^ (-b) * second 0 b c * (y ^ (-b))⁻¹ = x⁻¹ * y ^ (b + c) := by
    unfold second
    group
  have hs : Step (presentation n 0 b c) (pair (first n) (x⁻¹ * y ^ (b + c))) := by
    simpa only [presentation, pair_one, pair_update_one, he] using
      Step.conj (presentation n 0 b c) 1 (y ^ (-b))
  exact (Reachable.single hs).trans (power_second_solvable n (b + c))

/-- With middle exponent zero, the second relator is already in the power endpoint. -/
theorem zero_b_solvable (n : ℕ) (a c : ℤ) :
    Reachable (presentation n a 0 c) (standard 2) := by
  have he : second a 0 c = x⁻¹ * y ^ (a + c) := by unfold second; group
  simpa only [presentation, he] using power_second_solvable n (a + c)

/-- The first nonzero residue cell is the proved uniform family at `n=2`. -/
theorem one_one_solvable (c : ℤ) :
    Reachable (presentation 2 1 1 c) (standard 2) := by
  simpa using Uniform.uniform_family 2 c

/-- Inverting `y` sends the solved cell `(1,1)` to the residue cell `(1,2)`. -/
theorem one_two_solvable (c : ℤ) :
    Reachable (presentation 2 1 2 c) (standard 2) := by
  have hi : Reachable (presentation 2 (-1) (-1) 0) (standard 2) := by
    simpa using YInversion.solution 2 1 1 0 (one_one_solvable 0)
  have hr := (residue_solvable_iff 2 (-1) (-1) 0).mp hi
  have hs : Reachable (presentation 2 1 2 0) (standard 2) := by
    norm_num at hr
    exact hr
  exact shear_family 2 1 2 0 hs c

/-- All integer parameters of this three-exponent Miller–Schupp family at `n=2`. -/
theorem all_parameters_two (a b c : ℤ) :
    Reachable (presentation 2 a b c) (standard 2) := by
  apply (residue_solvable_iff 2 a b c).mpr
  change Reachable (presentation 2 (a % 2) (b % 3) 0) (standard 2)
  have ha₀ : 0 ≤ a % 2 := Int.emod_nonneg a (by decide)
  have ha₂ : a % 2 < 2 := by simpa using Int.emod_lt a (by decide : (2 : ℤ) ≠ 0)
  have hb₀ : 0 ≤ b % 3 := Int.emod_nonneg b (by decide)
  have hb₃ : b % 3 < 3 := by simpa using Int.emod_lt b (by decide : (3 : ℤ) ≠ 0)
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hb : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
  rcases ha with ha | ha
  · simpa only [ha] using zero_a_solvable 2 (b % 3) 0
  · rcases hb with hb | hb | hb
    · simpa only [ha, hb] using zero_b_solvable 2 1 0
    · simpa only [ha, hb] using one_one_solvable 0
    · simpa only [ha, hb] using one_two_solvable 0

/-- At `n=1`, the first-parameter residue has only the zero cell. -/
theorem all_parameters_one (a b c : ℤ) :
    Reachable (presentation 1 a b c) (standard 2) := by
  apply (residue_solvable_iff 1 a b c).mpr
  simpa using zero_a_solvable 1 (b % 2) 0

/-- The degenerate `n=0` relation is also handled by the proved period reduction. -/
theorem all_parameters_zero (a b c : ℤ) :
    Reachable (presentation 0 a b c) (standard 2) := by
  apply (residue_solvable_iff 0 a b c).mpr
  simpa using zero_b_solvable 0 a 0

theorem all_parameters_small (n : ℕ) (hn : n ≤ 2) (a b c : ℤ) :
    Reachable (presentation n a b c) (standard 2) := by
  have cases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases cases with rfl | rfl | rfl
  · exact all_parameters_zero a b c
  · exact all_parameters_one a b c
  · exact all_parameters_two a b c

end AC.MillerSchupp.ResidueClasses
