import ACSquareDiagonalFamilies

/-!
# Constructive solution of the degree-two root conjugacy family

The parity split supplies finite normal-closure witnesses throughout. No
quotient equality is used as an uncharged relator substitution.
-/

namespace AC.MillerSchupp.SquareFamily.P2
open AC.Certificate AC.Substitution AC.WordTransport

def root (k : ℤ) : Word 2 := y ^ (-k) * x ^ 2 * y ^ k * x⁻¹
def companion (s : ℤ) : Word 2 := y⁻¹ * (y ^ (-s) * x⁻¹ * y ^ s * x⁻¹)
def powerRelator (e : ℤ) : Word 2 := y⁻¹ * x ^ e

def doubleWitness (k : ℤ) : Witness (root k) (y ^ k * x * y ^ (-k)) (x ^ 2) where
  factors := [(y ^ k * x⁻¹, true)]
  sound := by dsimp [product, Factor.value, root]; group

def iteratedDouble (k : ℤ) : (m : ℕ) →
    Witness (root k) (y ^ (k * m) * x * y ^ (-(k * m))) (x ^ (2 ^ m))
  | 0 => Witness.ofEq _ (by simp)
  | m + 1 => by
    let a := (iteratedDouble k m).conj (y ^ k)
    let b := (doubleWitness k).pow (2 ^ m)
    exact (a.trans (b.change (by simp only [zpow_neg, conj_pow]) rfl)).change
      (by push_cast; group) (by rw [← pow_mul, pow_succ, Nat.mul_comm])

private theorem replace_first {r q z : Word 2} (w : Witness q r z) :
    Reachable (pair r q) (pair z q) := by
  simpa only [pair_update_zero] using
    (replace (pair r q) 0 1 (by decide) w.factors z w.sound).reachable

private theorem replace_second {r q z : Word 2} (w : Witness r q z) :
    Reachable (pair r q) (pair r z) := by
  simpa only [pair_update_one] using
    (replace (pair r q) 1 0 (by decide) w.factors z w.sound).reachable

private theorem conj_first (r q g z : Word 2) (h : g * r * g⁻¹ = z) :
    Reachable (pair r q) (pair z q) := by
  simpa only [pair_zero, pair_update_zero, h] using
    Reachable.single (Step.conj (pair r q) 0 g)

private theorem conj_second (r q g z : Word 2) (h : g * q * g⁻¹ = z) :
    Reachable (pair r q) (pair r z) := by
  simpa only [pair_one, pair_update_one, h] using
    Reachable.single (Step.conj (pair r q) 1 g)

/-- A power relation eliminates the stable letter for any root degree. -/
theorem power_finish (k e : ℤ) :
    Reachable (pair (root k) (powerRelator e)) (standard 2) := by
  let w : Witness (powerRelator e) y (x ^ e) :=
    ⟨[(1, true)], by dsimp [product, Factor.value, powerRelator]; group⟩
  let a := (((w.zpow (-k)).mul (Witness.refl _ (x ^ 2))).mul
    (w.zpow k)).mul (Witness.refl _ x⁻¹)
  let b : Witness (powerRelator e) (root k) x := a.change rfl (by group)
  have h₁ := replace_first b
  have h₂ : Reachable (pair x (powerRelator e)) (pair x y⁻¹) := by
    have h := (mulRight_zpow (pair x (powerRelator e)) 1 0 (by decide) (-e)).reachable
    simpa [powerRelator, mul_assoc] using h
  have h₃ : Reachable (pair x y⁻¹) (standard 2) := by
    have h := Reachable.single (Step.inv (pair x y⁻¹) 1)
    have he : pair x y = standard 2 := by ext i; fin_cases i <;> rfl
    simpa only [pair_one, pair_update_one, inv_inv, he] using h
  exact h₁.trans (h₂.trans h₃)

/-- Every height that is a nonnegative multiple of the root degree reduces to a power. -/
theorem multiple_root_solvable (p : ℤ) (m : ℕ) :
    Reachable (pair (root p) (companion (p * m))) (standard 2) := by
  let e : ℤ := -((2 : ℤ) ^ m + 1)
  let q : Word 2 := y ^ (p * (m : ℤ)) * companion (p * m) * y ^ (-(p * (m : ℤ)))
  have hc : Reachable (pair (root p) (companion (p * m))) (pair (root p) q) :=
    conj_second _ _ (y ^ (p * (m : ℤ))) _ (by dsimp [q]; group)
  let a := (Witness.refl (root p) (y⁻¹ * x⁻¹)).mul (iteratedDouble p m).inverse
  let b : Witness (root p) q (powerRelator e) := a.change
    (by dsimp [q, companion]; group)
    (by dsimp [powerRelator, e]; simp only [← zpow_natCast, Nat.cast_pow, Nat.cast_ofNat]; group)
  exact hc.trans ((replace_second b).trans (power_finish p e))

/-- One below a positive multiple of the root degree, the companion lowers that degree. -/
theorem predecessor_multiple_root_solvable (p : ℤ) (m : ℕ) :
    Reachable (pair (root p) (companion (p * m + (p - 1)))) (standard 2) := by
  let d : ℤ := (2 : ℤ) ^ m
  let q : Word 2 := y ^ (-p) * x⁻¹ * y ^ (p - 1) * x ^ (-d)
  let a := (Witness.refl (root p) (y⁻¹ * (y ^ (-(p - 1)) * x⁻¹ * y ^ (p - 1)))).mul
    (iteratedDouble p m).inverse
  let b : Witness (root p)
      (y ^ (p * (m : ℤ)) * companion (p * m + (p - 1)) * (y ^ (p * (m : ℤ)))⁻¹) q :=
    a.change (by dsimp [companion]; group)
      (by dsimp [q, d]; simp only [← zpow_natCast, Nat.cast_pow, Nat.cast_ofNat]; group)
  have hc := conj_second (root p) (companion (p * m + (p - 1))) (y ^ (p * (m : ℤ))) _ rfl
  have hq := replace_second b
  let v : Word 2 := x⁻¹ * y ^ (p - 1) * x ^ (-d)
  let w : Witness q (y ^ p) v :=
    ⟨[(1, true)], by dsimp [q, v, product, Factor.value]; group⟩
  let c := ((w.inverse.mul (Witness.refl q (x ^ 2))).mul w).mul (Witness.refl q x⁻¹)
  let c' : Witness q (root p) (x ^ d * root (p - 1) * (x ^ d)⁻¹) :=
    c.change (by dsimp [root]; group) (by dsimp [root, v]; group)
  have hr := replace_first c'
  have hn := conj_first (x ^ d * root (p - 1) * (x ^ d)⁻¹) q (x ^ (-d)) (root (p - 1)) (by group)
  let e : ℤ := -(2 * d + 1)
  let z := (Witness.refl (root (p - 1)) (y⁻¹ * x⁻¹)).mul ((doubleWitness (p - 1)).zpow (-d))
  let z' : Witness (root (p - 1)) (y ^ (p - 1) * q * (y ^ (p - 1))⁻¹) (powerRelator e) := z.change
    (by dsimp [q]; simp only [zpow_neg, conj_zpow]; group) (by dsimp [powerRelator, e]; group)
  have hy := conj_second (root (p - 1)) q (y ^ (p - 1)) (y ^ (p - 1) * q * (y ^ (p - 1))⁻¹) rfl
  exact hc.trans (hq.trans (hr.trans (hn.trans (hy.trans
    ((replace_second z').trans (power_finish (p - 1) e))))))

theorem even_root_solvable (m : ℕ) :
    Reachable (pair (root 2) (companion (2 * m))) (standard 2) :=
  multiple_root_solvable 2 m

theorem odd_root_solvable (m : ℕ) :
    Reachable (pair (root 2) (companion (2 * m + 1))) (standard 2) := by
  simpa using predecessor_multiple_root_solvable 2 m

/-- Every nonnegative height has an explicit finite ordinary AC solution. -/
theorem root_solvable (s : ℕ) :
    Reachable (pair (root 2) (companion s)) (standard 2) := by
  have h : s = 2 * (s / 2) ∨ s = 2 * (s / 2) + 1 := by omega
  rcases h with h | h
  · have he : (s : ℤ) = 2 * ((s / 2 : ℕ) : ℤ) := by exact_mod_cast h
    rw [he]
    exact even_root_solvable (s / 2)
  · have he : (s : ℤ) = 2 * ((s / 2 : ℕ) : ℤ) + 1 := by exact_mod_cast h
    rw [he]
    exact odd_root_solvable (s / 2)

end AC.MillerSchupp.SquareFamily.P2
