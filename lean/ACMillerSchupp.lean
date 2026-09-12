import ACWordTransport
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Group
import Mathlib.Tactic.FinCases

/-!
# Explicit Miller–Schupp families

The integer shear transports a complete ordinary certificate, with a separately
proved ordinary normalization of the image of the standard tuple.
-/

namespace AC.MillerSchupp

open AC.Certificate AC.WordTransport

def x : Word 2 := FreeGroup.of 0
def y : Word 2 := FreeGroup.of 1
def pair (r q : Word 2) : Relators 2 := fun i => if i = 0 then r else q

def first (n : ℕ) : Word 2 := x⁻¹ * y ^ n * x * y ^ (-(n + 1 : ℤ))

/-- The second relator is `x⁻¹ w`, with the entire right-hand side `w` displayed. -/
def second (a b c : ℤ) : Word 2 := x⁻¹ * y ^ a * x * y ^ b * x⁻¹ * y ^ c

def presentation (n : ℕ) (a b c : ℤ) : Relators 2 := pair (first n) (second a b c)

def shear (k : ℤ) : Word 2 →* Word 2 := FreeGroup.lift (pair (y ^ k * x) y)

@[simp] theorem shear_x (k : ℤ) : shear k x = y ^ k * x := by
  simp [shear, x, pair]

@[simp] theorem shear_y (k : ℤ) : shear k y = y := by
  simp [shear, y, pair]

theorem shear_first (k : ℤ) (n : ℕ) : shear k (first n) = first n := by
  simp only [first, map_mul, map_inv, map_pow, map_zpow, shear_x, shear_y]
  group

theorem shear_second (k a b c : ℤ) : shear k (second a b c) = second a b (c - k) := by
  simp only [second, map_mul, map_inv, map_zpow, shear_x, shear_y]
  group

theorem shear_presentation (k : ℤ) (n : ℕ) (a b c : ℤ) :
    applyHom (shear k) (presentation n a b c) = presentation n a b (c - k) := by
  ext i
  fin_cases i <;> simp [applyHom, presentation, pair, shear_first, shear_second]

theorem shear_standard (k : ℤ) :
    applyHom (shear k) (standard 2) = pair (y ^ k * x) y := by
  ext i
  fin_cases i <;> simp [applyHom, standard, pair, shear, x, y]

/-- The image basis is solved in at most `|k|+3` official primitives. -/
theorem shear_standard_steps (k : ℤ) :
    ∃ l ≤ k.natAbs + 3, Steps (applyHom (shear k) (standard 2)) l (standard 2) := by
  rw [shear_standard]
  have h₁ : Steps (pair (y ^ k * x) y) 1 (pair (x * y ^ k) y) := by
    convert Steps.single (Step.conj (pair (y ^ k * x) y) 0 x) using 1
    ext i
    fin_cases i <;> simp [pair, mul_assoc]
  have h₂ := mulRight_zpow (pair (x * y ^ k) y) 0 1 (by decide) (-k)
  have he : Function.update (pair (x * y ^ k) y) 0
      (pair (x * y ^ k) y 0 * pair (x * y ^ k) y 1 ^ (-k)) = standard 2 := by
    ext i
    fin_cases i <;> simp [pair, standard, x, y, mul_assoc]
  rw [he] at h₂
  refine ⟨_, ?_, h₁.trans h₂⟩
  simp only [Int.natAbs_neg]
  split_ifs <;> omega

/-- One checked seed implies every integer value of the final exponent. -/
theorem shear_family (n : ℕ) (a b c₀ : ℤ)
    (h : Reachable (presentation n a b c₀) (standard 2)) (c : ℤ) :
    Reachable (presentation n a b c) (standard 2) := by
  obtain ⟨l, _, hl⟩ := shear_standard_steps (c₀ - c)
  have hs := solvable_hom (shear (c₀ - c)) _ h hl.reachable
  simpa only [shear_presentation, sub_sub_cancel] using hs

/-- The whole-path transport preserves its input count; only the endpoint adds cost. -/
theorem shear_family_counted (n : ℕ) (a b c₀ : ℤ) {L : ℕ}
    (h : Steps (presentation n a b c₀) L (standard 2)) (c : ℤ) :
    ∃ l ≤ L + (c₀ - c).natAbs + 3, Steps (presentation n a b c) l (standard 2) := by
  obtain ⟨l, hb, hl⟩ := shear_standard_steps (c₀ - c)
  have hs := (steps_hom (shear (c₀ - c)) h).trans hl
  refine ⟨L + l, by omega, ?_⟩
  simpa only [shear_presentation, sub_sub_cancel] using hs

end AC.MillerSchupp
