import ACDiagonalDescent

/-!
# Parameter transport and diagonal families

The complementary exponent can be exchanged by a fixed substitution. This
transports the new diagonal recurrence to both signs of the square family
and then to the original presentations through the existing pinches.
-/

namespace AC.MillerSchupp.SquareFamily

open AC.Certificate AC.Substitution AC.WordTransport

/-- One supplied factor replaces the central power by the square. -/
def squarePowerWitness (s k : ℤ) : Witness (square s k) (y ^ (s + k)) (x ^ 2) where
  factors := [(y ^ (-(s + k)), true)]
  sound := by
    dsimp [product, Factor.value, square]
    group

/-- The square supplies a two-factor commutation witness for every x-power. -/
def squareCommuteWitness (s k t : ℤ) :
    Witness (square s k) (y ^ (s + k) * x ^ t) (x ^ t * y ^ (s + k)) := by
  let b := squarePowerWitness s k
  let left := b.mul (Witness.refl (square s k) (x ^ t))
  let right := (Witness.refl (square s k) (x ^ t)).mul b
  exact left.trans (right.reverse.change (by group) rfl)

/-- Four explicit factors supply the full period, with the square fixed. -/
def squarePeriodWitness (p s k : ℤ) :
    Witness (square s k) (relation (p + (s + k)) s) (relation p s) := by
  let c₁ := (squareCommuteWitness s k 1).mul
    (Witness.refl (square s k) (y ^ (-s) * x⁻¹))
  let c₂ := (Witness.refl (square s k) (x * y ^ (-s))).mul
    (squareCommuteWitness s k (-1))
  let middle := c₁.trans (c₂.change (by group) rfl)
  let whole := ((Witness.refl (square s k) (x * y ^ p)).mul middle).mul
    (Witness.refl (square s k) (y ^ (-p) * y ^ (-(s + k))))
  exact whole.change (by dsimp [relation]; group) (by dsimp [relation]; group)

theorem squarePeriodWitness_length (p s k : ℤ) :
    (squarePeriodWitness p s k).factors.length = 4 := rfl

theorem squarePeriodWitness_cost (p s k : ℤ) :
    cost (squarePeriodWitness p s k).factors = 16 := rfl

theorem square_period_steps (p s k : ℤ) :
    Steps (pair (square s k) (relation (p + (s + k)) s)) 16
      (pair (square s k) (relation p s)) := by
  let w := squarePeriodWitness p s k
  simpa only [w, pair_update_one, squarePeriodWitness_cost] using
    replace (pair (square s k) (relation (p + (s + k)) s)) 1 0 (by decide)
      w.factors _ w.sound

theorem square_period (p s k t : ℤ) :
    Reachable (pair (square s k) (relation p s)) (standard 2) ↔
      Reachable (pair (square s k) (relation (p + (s + k) * t) s)) (standard 2) := by
  induction t using Int.induction_on with
  | zero => simp
  | succ t ih =>
    have h := ih.trans
      (ResidueClasses.path_solvable_iff (square_period_steps (p + (s + k) * t) s k).reachable).symm
    have he : p + (s + k) * (t : ℤ) + (s + k) = p + (s + k) * ((t : ℤ) + 1) := by ring
    simpa only [he] using h
  | pred t ih =>
    have hs := square_period_steps (p + (s + k) * (-(t : ℤ) - 1)) s k
    have he : p + (s + k) * (-(t : ℤ) - 1) + (s + k) = p + (s + k) * (-(t : ℤ)) := by ring
    rw [he] at hs
    exact ih.trans (ResidueClasses.path_solvable_iff hs.reachable)

/-- The zero residue has a direct power elimination, for every natural s. -/
theorem zero_square_solvable (s : ℕ) :
    Reachable (pair (square s (s + 1)) (relation 0 s)) (standard 2) := by
  let q : Word 2 := x * y ^ (-(s : ℤ))
  have hq : x⁻¹ * relation 0 s * (x⁻¹)⁻¹ = q := by dsimp [relation, q]; group
  have hi := Reachable.single (Step.conj
    (pair (square s (s + 1)) (relation 0 s)) 1 x⁻¹)
  simp only [pair_one, pair_update_one, hq] at hi
  let w : Witness q x (y ^ (s : ℤ)) :=
    ⟨[(x⁻¹, false)], by dsimp [product, Factor.value, q]; group⟩
  let w' := (w.pow 2).mul (Witness.refl q (y ^ (-(s + (s + 1) : ℤ))))
  have hsource : x ^ 2 * y ^ (-(s + (s + 1) : ℤ)) = square s (s + 1) := rfl
  have htarget : (y ^ (s : ℤ)) ^ 2 * y ^ (-(s + (s + 1) : ℤ)) = y⁻¹ := by group
  let hw := w'.change hsource htarget
  have hr := (replace (pair (square s (s + 1)) q) 0 1 (by decide)
    hw.factors y⁻¹ hw.sound).reachable
  simp only [pair_update_zero] at hr
  have hinv := Reachable.single (Step.inv (pair y⁻¹ q) 0)
  simp only [pair_zero, pair_update_zero, inv_inv] at hinv
  have hmul := (mulRight_zpow (pair y q) 1 0 (by decide) (s : ℤ)).reachable
  have hmul' : Reachable (pair y q) (pair y x) := by
    simpa [q, mul_assoc] using hmul
  have hs : pair x y = standard 2 := by ext i; fin_cases i <;> rfl
  have hswap : Reachable (pair y x) (pair x y) := by
    have h := (Steps.swap (pair y x) 0 1 (by decide)).reachable
    convert h using 1
    ext i
    fin_cases i <;> rfl
  exact hi.trans (hr.trans (hinv.trans (hmul'.trans (by simpa only [hs] using hswap))))

/-- Exchange the complementary exponents while preserving the square relator. -/
theorem complement_steps (p s k : ℤ) :
    Steps (pair (square s k) (relation p s)) 13
      (pair (square s k) (relation p k)) := by
  let a := y ^ p * x * y ^ (-s)
  let e := x⁻¹ * y ^ p * x * y ^ s * x⁻¹ * y ^ (-p)
  let fs : List (Factor 2) :=
    [(a * x⁻¹ * y ^ (-p), true), (a * x⁻¹, false), (a, true)]
  have he : x⁻¹ * (relation p s)⁻¹ * (x⁻¹)⁻¹ = e := by
    dsimp [relation, e]
    group
  have h₁ : Steps (pair (square s k) (relation p s)) 2 (pair (square s k) e) := by
    have hi := Steps.single (Step.inv (pair (square s k) (relation p s)) 1)
    have hc := Steps.single (Step.conj (pair (square s k) (relation p s)⁻¹) 1 x⁻¹)
    simp only [pair_one, pair_update_one, he] at hi hc
    exact hi.trans hc
  have hw : e * product (square s k) fs = relation p k := by
    dsimp [fs, product, Factor.value, e, a, square, relation]
    group
  have h₂ := replace (pair (square s k) e) 1 0 (by decide) fs (relation p k) hw
  simp only [pair_update_one] at h₂
  have hcost : cost fs = 11 := rfl
  rw [hcost] at h₂
  exact h₁.trans h₂

/-- A mirror presentation reaches the negative first exponent in nine primitives. -/
theorem mirror_negative_steps (p s k : ℤ) :
    Steps (pair (square s k) (mirrorRelation p s)) 9
      (pair (square s k) (relation (-p) s)) := by
  let g := (x * y ^ p)⁻¹
  let e := x * y ^ (-p) * x⁻¹ * y ^ (-s) * x * y ^ p
  let fs : List (Factor 2) :=
    [(y ^ (-p) * x⁻¹ * y ^ s, true), (y ^ (-p) * x⁻¹, false)]
  have he : g * mirrorRelation p s * g⁻¹ = e := by
    dsimp [g, mirrorRelation, e]
    group
  have h₁ : Steps (pair (square s k) (mirrorRelation p s)) 1
      (pair (square s k) e) := by
    simpa only [pair_one, pair_update_one, he] using
      Steps.single (Step.conj (pair (square s k) (mirrorRelation p s)) 1 g)
  have hw : e * product (square s k) fs = relation (-p) s := by
    dsimp [fs, product, Factor.value, e, square, relation]
    group
  have h₂ := replace (pair (square s k) e) 1 0 (by decide) fs (relation (-p) s) hw
  simp only [pair_update_one] at h₂
  have hcost : cost fs = 8 := rfl
  rw [hcost] at h₂
  exact h₁.trans h₂

/-- Reflection changes the sign of the first exponent in the solution family. -/
theorem negative_solvable (p s k : ℤ)
    (h : Reachable (pair (square s k) (relation p s)) (standard 2)) :
    Reachable (pair (square s k) (relation (-p) s)) (standard 2) :=
  (ResidueClasses.reverse_path (mirror_negative_steps p s k).reachable).trans
    (mirror_solvable s k p h)

/-- The five covered residue representatives, with all integer periods included. -/
theorem covered_positive (m : ℕ) (p : ℤ)
    (hp : ∃ r t : ℤ, p = r + (2 * m + 1) * t ∧
      (r = 0 ∨ r = 1 ∨ r = -1 ∨ r = m ∨ r = -(m : ℤ))) :
    Reachable (pair (square m (m + 1)) (relation p m)) (standard 2) := by
  obtain ⟨r, t, hp, hr⟩ := hp
  have he : p = r + ((m : ℤ) + (m + 1)) * t := by rw [hp]; ring
  rw [he]
  apply (square_period r m (m + 1) t).mp
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact zero_square_solvable m
  · exact even_square_solvable m
  · exact negative_solvable 1 m (m + 1) (even_square_solvable m)
  · exact Diagonal.solvable m
  · exact negative_solvable m m (m + 1) (Diagonal.solvable m)

theorem covered_negative (m : ℕ) (p : ℤ)
    (hp : ∃ r t : ℤ, p = r + (2 * m + 1) * t ∧
      (r = 0 ∨ r = 1 ∨ r = -1 ∨ r = m ∨ r = -(m : ℤ))) :
    Reachable (pair (square (m + 1) m) (relation p (m + 1))) (standard 2) := by
  have he : square (m + 1) m = square m (m + 1) := by
    unfold square
    congr 2
    omega
  have ht := (complement_steps p (m + 1) m).reachable
  rw [he] at ht ⊢
  exact ht.trans (covered_positive m p hp)

/-- Both sign choices now have a diagonal solution. -/
theorem complementary_diagonal (s : ℕ) :
    Reachable (pair (square (s + 1) s) (relation s (s + 1))) (standard 2) := by
  have he : square (s + 1) s = square s (s + 1) := by
    unfold square
    congr 2
    omega
  rw [he]
  have ht := complement_steps s (s + 1) s
  rw [he] at ht
  exact ht.reachable.trans (Diagonal.solvable s)

/-- The general square solution pulls back through the odd pinch. -/
theorem odd_of_square (m : ℕ) (p c : ℤ)
    (h : Reachable (pair (square (m + 1) m) (relation p (m + 1))) (standard 2)) :
    Reachable (presentation (2 * m + 1) p (m + 1) c) (standard 2) := by
  apply shear_family (2 * m + 1) p (m + 1) 0 _ c
  have ht := solvable_hom (rightShear (-p)) _ h (rightShear_standard (-p))
  have hp : applyHom (rightShear (-p))
      (pair (square (m + 1) m) (relation p (m + 1))) =
      pair ((x * y ^ (-p)) ^ 2 * y ^ (-(2 * m + 1 : ℤ)))
        (x * (second p (m + 1) 0)⁻¹ * x⁻¹) := by
    ext i
    fin_cases i <;> simp [applyHom, pair, square, relation, second, pow_two] <;> group
  rw [hp] at ht
  have hi := Reachable.single (Step.inv
    (pair ((x * y ^ (-p)) ^ 2 * y ^ (-(2 * m + 1 : ℤ))) (second p (m + 1) 0)) 1)
  have hc := Reachable.single (Step.conj
    (pair ((x * y ^ (-p)) ^ 2 * y ^ (-(2 * m + 1 : ℤ))) (second p (m + 1) 0)⁻¹) 1 x)
  simp only [pair_one, pair_update_one] at hi hc
  have hn : ((2 * m + 1 : ℕ) : ℤ) = 2 * m + 1 := by omega
  have hpinch := right_pinch (2 * m + 1) p (m + 1) (by omega)
  rw [hn] at hpinch
  exact hpinch.trans (hi.trans (hc.trans ht))

/-- The general square solution pulls back through the even mirror pinch. -/
theorem even_of_square (m : ℕ) (p c : ℤ)
    (h : Reachable (pair (square m (m + 1)) (relation p m)) (standard 2)) :
    Reachable (presentation (2 * m) m p c) (standard 2) := by
  apply shear_family (2 * m) m p 0 _ c
  have ht := solvable_hom (rightShear (-p)) _ (mirror_solvable m (m + 1) p h)
    (rightShear_standard (-p))
  have hp : applyHom (rightShear (-p))
      (pair (square m (m + 1)) (mirrorRelation p m)) =
      pair ((x * y ^ (-p)) ^ 2 * y ^ (-(2 * m + 1 : ℤ)))
        (x * (second m p 0)⁻¹ * x⁻¹) := by
    ext i
    fin_cases i <;> simp [applyHom, pair, square, mirrorRelation, second, pow_two] <;> group
  rw [hp] at ht
  have hi := Reachable.single (Step.inv
    (pair ((x * y ^ (-p)) ^ 2 * y ^ (-(2 * m + 1 : ℤ))) (second m p 0)) 1)
  have hc := Reachable.single (Step.conj
    (pair ((x * y ^ (-p)) ^ 2 * y ^ (-(2 * m + 1 : ℤ))) (second m p 0)⁻¹) 1 x)
  simp only [pair_one, pair_update_one] at hi hc
  have hn : ((2 * m : ℕ) : ℤ) + 1 = 2 * m + 1 := by omega
  have hpinch := left_pinch (2 * m) m p (by omega)
  rw [hn] at hpinch
  exact hpinch.trans (hi.trans (hc.trans ht))

/-- A new all-parameter diagonal family in the original coordinates. -/
theorem even_diagonal_family (m : ℕ) (c : ℤ) :
    Reachable (presentation (2 * m) m m c) (standard 2) :=
  even_of_square m m c (Diagonal.solvable m)

/-- The complementary sign gives the adjacent diagonal. -/
theorem odd_diagonal_family (m : ℕ) (c : ℤ) :
    Reachable (presentation (2 * m + 1) m (m + 1) c) (standard 2) :=
  odd_of_square m m c (complementary_diagonal m)

theorem even_negative_diagonal_family (m : ℕ) (c : ℤ) :
    Reachable (presentation (2 * m) m (-(m : ℤ)) c) (standard 2) :=
  even_of_square m (-m) c (negative_solvable m m (m + 1) (Diagonal.solvable m))

theorem odd_negative_diagonal_family (m : ℕ) (c : ℤ) :
    Reachable (presentation (2 * m + 1) (-(m : ℤ)) (m + 1) c) (standard 2) :=
  odd_of_square m (-m) c
    (negative_solvable m (m + 1) m (complementary_diagonal m))

end AC.MillerSchupp.SquareFamily
