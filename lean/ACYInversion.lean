import ACMillerSchuppCriterion

/-!
# Counted transport under inversion of the second generator

The generator map is applied to a whole supplied solution. Two actual moves
adjust the first relator, and one actual move normalizes the image basis.
The map itself is not introduced as an additional allowed AC move.
-/

namespace AC.MillerSchupp.YInversion

open AC.Certificate AC.WordTransport

def yInversion : Word 2 →* Word 2 := FreeGroup.lift (pair x y⁻¹)

@[simp] theorem map_x : yInversion x = x := by simp [yInversion, x, pair]

@[simp] theorem map_y : yInversion y = y⁻¹ := by simp [yInversion, y, pair]

theorem first_image (n : ℕ) :
    yInversion (first n) =
      y ^ (-(n + 1 : ℤ)) * (first n)⁻¹ * y ^ (n + 1 : ℤ) := by
  simp only [first, map_mul, map_inv, map_pow, map_zpow, map_x, map_y]
  group

@[simp] theorem second_image (a b c : ℤ) :
    yInversion (second a b c) = second (-a) (-b) (-c) := by
  simp only [second, map_mul, map_inv, map_zpow, map_x, map_y]
  group

theorem presentation_image (n : ℕ) (a b c : ℤ) :
    applyHom yInversion (presentation n a b c) =
      pair (yInversion (first n)) (second (-a) (-b) (-c)) := by
  ext i
  fin_cases i <;> simp [applyHom, presentation, second_image]

theorem standard_image : applyHom yInversion (standard 2) = pair x y⁻¹ := by
  ext i
  fin_cases i <;> simp [applyHom, standard, x, y, yInversion, pair]

/-- The normalized image basis requires exactly one inversion. -/
theorem standard_steps :
    Steps (applyHom yInversion (standard 2)) 1 (standard 2) := by
  rw [standard_image]
  have he : pair x y = standard 2 := by
    ext i
    fin_cases i <;> simp [pair, standard, x, y]
  simpa only [pair_one, pair_update_one, inv_inv, he] using
    Steps.single (Step.inv (pair x y⁻¹) 1)

/-- Enter the image presentation by two official operations on its first slot. -/
theorem to_image_steps (n : ℕ) (a b c : ℤ) :
    Steps (presentation n (-a) (-b) (-c)) 2
      (applyHom yInversion (presentation n a b c)) := by
  rw [presentation_image]
  have h₁ : Steps (presentation n (-a) (-b) (-c)) 1
      (pair (first n)⁻¹ (second (-a) (-b) (-c))) := by
    simpa only [presentation, pair_zero, pair_update_zero] using
      Steps.single (Step.inv (presentation n (-a) (-b) (-c)) 0)
  have h₂ : Step (pair (first n)⁻¹ (second (-a) (-b) (-c)))
      (pair (yInversion (first n)) (second (-a) (-b) (-c))) := by
    have he : y ^ (-(n + 1 : ℤ)) * (first n)⁻¹ *
        (y ^ (-(n + 1 : ℤ)))⁻¹ = yInversion (first n) := by
      rw [first_image]
      group
    simpa only [pair_zero, pair_update_zero, he] using
      Step.conj (pair (first n)⁻¹ (second (-a) (-b) (-c))) 0
        (y ^ (-(n + 1 : ℤ)))
  exact h₁.tail h₂

/-- Restore the defining first relator after applying generator inversion. -/
theorem restore_first_steps (n : ℕ) (a b c : ℤ) :
    Steps (applyHom yInversion (presentation n a b c)) 2
      (presentation n (-a) (-b) (-c)) := by
  rw [presentation_image]
  have h₁ : Steps (pair (yInversion (first n)) (second (-a) (-b) (-c))) 1
      (pair (y ^ (-(n + 1 : ℤ)) * first n * y ^ (n + 1 : ℤ))
        (second (-a) (-b) (-c))) := by
    have he : (yInversion (first n))⁻¹ =
        y ^ (-(n + 1 : ℤ)) * first n * y ^ (n + 1 : ℤ) := by
      rw [first_image]
      group
    simpa only [pair_zero, pair_update_zero, he] using
      Steps.single (Step.inv (pair (yInversion (first n))
        (second (-a) (-b) (-c))) 0)
  have h₂ : Step (pair (y ^ (-(n + 1 : ℤ)) * first n * y ^ (n + 1 : ℤ))
      (second (-a) (-b) (-c))) (presentation n (-a) (-b) (-c)) := by
    have he : y ^ (n + 1 : ℤ) *
        (y ^ (-(n + 1 : ℤ)) * first n * y ^ (n + 1 : ℤ)) *
          (y ^ (n + 1 : ℤ))⁻¹ = first n := by group
    simpa only [presentation, pair_zero, pair_update_zero, he] using
      Step.conj (pair (y ^ (-(n + 1 : ℤ)) * first n * y ^ (n + 1 : ℤ))
        (second (-a) (-b) (-c))) 0 (y ^ (n + 1 : ℤ))
  exact h₁.tail h₂

/-- Whole-path transport adds exactly the three explicitly accounted-for moves. -/
theorem solution_steps (n : ℕ) (a b c : ℤ) {L : ℕ}
    (h : Steps (presentation n a b c) L (standard 2)) :
    Steps (presentation n (-a) (-b) (-c)) (L + 3) (standard 2) := by
  have ht := (to_image_steps n a b c).trans ((steps_hom yInversion h).trans standard_steps)
  convert ht using 1
  omega

theorem solution (n : ℕ) (a b c : ℤ)
    (h : Reachable (presentation n a b c) (standard 2)) :
    Reachable (presentation n (-a) (-b) (-c)) (standard 2) :=
  (to_image_steps n a b c).reachable.trans
    ((reachable_hom yInversion h).trans standard_steps.reachable)

theorem solvable_iff (n : ℕ) (a b c : ℤ) :
    Reachable (presentation n a b c) (standard 2) ↔
      Reachable (presentation n (-a) (-b) (-c)) (standard 2) := by
  constructor
  · exact solution n a b c
  · intro h
    simpa only [neg_neg] using solution n (-a) (-b) (-c) h

end AC.MillerSchupp.YInversion
