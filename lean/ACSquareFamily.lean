import ACResidueClasses

/-!
# Constructive square-family reductions

The quotient-two pinch and the fixed MS1 entry are based on the square-family
analysis at research/n3-square-family, commit 5ccd137. Every coordinate map
transports a complete path and has a separately supplied standard endpoint.
The MS1 finish reuses the constructed common-height witnesses.
-/

namespace AC.MillerSchupp.SquareFamily

open AC.Certificate AC.WordTransport AC.Substitution

private theorem inv_first (r q : Word 2) : Reachable (pair r q) (pair r⁻¹ q) := by
  simpa using Reachable.single (Step.inv (pair r q) 0)

private theorem inv_second (r q : Word 2) : Reachable (pair r q) (pair r q⁻¹) := by
  simpa using Reachable.single (Step.inv (pair r q) 1)

private theorem conj_first (r q g : Word 2) :
    Reachable (pair r q) (pair (g * r * g⁻¹) q) := by
  simpa using Reachable.single (Step.conj (pair r q) 0 g)

private theorem conj_second (r q g : Word 2) :
    Reachable (pair r q) (pair r (g * q * g⁻¹)) := by
  simpa using Reachable.single (Step.conj (pair r q) 1 g)

private theorem swapBoth_reachable {R S : Relators 2} (h : Reachable R S) :
    Reachable (Uniform.swapBoth R) (Uniform.swapBoth S) := by
  induction h with
  | refl => exact .refl _
  | tail _ step ih =>
    exact ih.trans (.single (step_reindex (Equiv.swap 0 1)
      (step_hom Uniform.swapGenerators step)))

def square (s k : ℤ) : Word 2 := x ^ 2 * y ^ (-(s + k))
def relation (p s : ℤ) : Word 2 := x * y ^ p * x * y ^ (-s) * x⁻¹ * y ^ (-p)
def stage (k : ℤ) : Word 2 := x * y ^ (-k) * x * y⁻¹ * x⁻¹ * y
def entryFirst (s k : ℤ) : Word 2 := x * y ^ k * x * y ^ (-s)
def entrySecond : Word 2 := x ^ 2 * y⁻¹ * x⁻¹ * y
def core (m : ℕ) (t : ℤ) : Word 2 := y⁻¹ * (y ^ (-(m : ℤ)) * x ^ t * y ^ (m : ℤ) * x ^ t)

/-- The fixed substitution uses the square relator once and restores it. -/
theorem stage_entry (s k : ℤ) :
    Reachable (pair (square s k) (relation 1 s)) (pair (square s k) (stage k)) := by
  let g := (y ^ (-s) * x⁻¹ * y⁻¹)⁻¹ * x ^ (-2 : ℤ)
  let q' := x * y * x⁻¹ * y ^ k * x⁻¹ * y⁻¹
  have he : relation 1 s * product (square s k) [(g, false)] = q' := by
    simp only [product, Factor.value, Bool.false_eq_true, ↓reduceIte, mul_one]
    dsimp [relation, square, q', g]
    group
  have h := (replace (pair (square s k) (relation 1 s)) 1 0 (by decide)
    [(g, false)] q' he).reachable
  simp only [pair_update_one] at h
  have he' : y⁻¹ * q'⁻¹ * (y⁻¹)⁻¹ = stage k := by dsimp [q', stage]; group
  have h' := (inv_second (square s k) q').trans (conj_second (square s k) q'⁻¹ y⁻¹)
  rw [he'] at h'
  exact h.trans h'

/-- The common-height witness supplies all signed two-block MS1 endpoints. -/
theorem core_solvable (m : ℕ) (t : ℤ) :
    Reachable (pair (core m t) entrySecond⁻¹) (standard 2) := by
  have h := swapBoth_reachable (Divisibility.family_solvable 1 0 [(m, t), (0, t)])
  rw [Uniform.swapBoth_pair, Uniform.swapBoth_standard] at h
  have hc : Uniform.swapGenerators
      (x⁻¹ * Divisibility.familyWord 1 0 [(m, t), (0, t)]) = core m t := by
    simp [Divisibility.familyWord, Divisibility.block, core]
  have hb : Uniform.swapGenerators (first 1) = entrySecond⁻¹ := by
    simp only [first, entrySecond, map_mul, map_inv, map_pow, map_zpow,
      Uniform.swapGenerators_x, Uniform.swapGenerators_y]
    group
  rwa [hc, hb] at h

/-- The odd-sign entry is a positive two-block MS1 word. -/
theorem odd_entry_solvable (m : ℕ) :
    Reachable (pair (entryFirst (m + 1) m) entrySecond) (standard 2) := by
  have he : y ^ (-(m + 1 : ℤ)) * entryFirst (m + 1) m *
      (y ^ (-(m + 1 : ℤ)))⁻¹ = core m 1 := by
    unfold entryFirst core
    group
  have h := conj_first (entryFirst (m + 1) m) entrySecond (y ^ (-(m + 1 : ℤ)))
  rw [he] at h
  exact h.trans ((inv_second (core m 1) entrySecond).trans (core_solvable m 1))

/-- The even-sign entry retains two negative exponents in its MS1 word. -/
theorem even_entry_solvable (m : ℕ) :
    Reachable (pair (entryFirst m (m + 1)) entrySecond) (standard 2) := by
  let g := (y ^ (m : ℤ) * x⁻¹)⁻¹
  have he : g * (entryFirst m (m + 1))⁻¹ * g⁻¹ = core m (-1) := by
    dsimp [g, entryFirst, core]
    group
  have h := (inv_first (entryFirst m (m + 1)) entrySecond).trans
    (conj_first (entryFirst m (m + 1))⁻¹ entrySecond g)
  rw [he] at h
  exact h.trans ((inv_second (core m (-1)) entrySecond).trans (core_solvable m (-1)))

/-- Pull back the complete sheared solution, including its image basis. -/
theorem square_of_entry (s k : ℤ)
    (h : Reachable (pair (entryFirst s k) entrySecond) (standard 2)) :
    Reachable (pair (square s k) (relation 1 s)) (standard 2) := by
  obtain ⟨_, _, hend⟩ := shear_standard_steps (-k)
  have ht := solvable_hom (shear (-k)) _ h hend.reachable
  have ha : shear (-k) (entryFirst s k) = y ^ (-k) * square s k * (y ^ (-k))⁻¹ := by
    simp only [entryFirst, square, map_mul, map_zpow, shear_x, shear_y, pow_two]
    group
  have hb : shear (-k) entrySecond = y ^ (-k) * stage k * (y ^ (-k))⁻¹ := by
    simp only [entrySecond, stage, map_mul, map_inv, shear_x, shear_y, pow_two]
    group
  have hp : applyHom (shear (-k)) (pair (entryFirst s k) entrySecond) =
      pair (y ^ (-k) * square s k * (y ^ (-k))⁻¹)
        (y ^ (-k) * stage k * (y ^ (-k))⁻¹) := by
    ext i
    fin_cases i <;> simp [applyHom, ha, hb]
  rw [hp] at ht
  exact (stage_entry s k).trans
    ((conj_first (square s k) (stage k) (y ^ (-k))).trans
      ((conj_second (y ^ (-k) * square s k * (y ^ (-k))⁻¹) (stage k)
        (y ^ (-k))).trans ht))

theorem odd_square_solvable (m : ℕ) :
    Reachable (pair (square (m + 1) m) (relation 1 (m + 1))) (standard 2) :=
  square_of_entry (m + 1) m (odd_entry_solvable m)

theorem even_square_solvable (m : ℕ) :
    Reachable (pair (square m (m + 1)) (relation 1 m)) (standard 2) :=
  square_of_entry m (m + 1) (even_entry_solvable m)

def invertGenerators : Word 2 →* Word 2 := FreeGroup.lift (pair x⁻¹ y⁻¹)

@[simp] theorem invertGenerators_x : invertGenerators x = x⁻¹ := by
  simp [invertGenerators, x, pair]

@[simp] theorem invertGenerators_y : invertGenerators y = y⁻¹ := by
  simp [invertGenerators, y, pair]

def mirrorRelation (p s : ℤ) : Word 2 :=
  x * y ^ p * x * y ^ (-p) * x⁻¹ * y ^ (-s)

/-- Reflection is implemented by whole-path generator inversion and four entry moves. -/
theorem mirror_solvable (s k p : ℤ)
    (h : Reachable (pair (square s k) (relation p s)) (standard 2)) :
    Reachable (pair (square s k) (mirrorRelation p s)) (standard 2) := by
  have hend : Reachable (applyHom invertGenerators (standard 2)) (standard 2) := by
    have he : applyHom invertGenerators (standard 2) = pair x⁻¹ y⁻¹ := by
      ext i
      fin_cases i <;> simp [applyHom, standard, invertGenerators, pair, x, y]
    rw [he]
    have hs : pair x y = standard 2 := by ext i; fin_cases i <;> rfl
    simpa only [inv_inv, hs] using
      (inv_first x⁻¹ y⁻¹).trans (inv_second x y⁻¹)
  have ht := solvable_hom invertGenerators _ h hend
  let g := (x * y ^ p * x)⁻¹
  have ha : y ^ (-(s + k)) * (square s k)⁻¹ * (y ^ (-(s + k)))⁻¹ =
      invertGenerators (square s k) := by
    simp only [square, map_mul, map_pow, map_zpow, invertGenerators_x, invertGenerators_y]
    group
  have hb : g * (mirrorRelation p s)⁻¹ * g⁻¹ = invertGenerators (relation p s) := by
    simp only [relation, map_mul, map_inv, map_zpow, invertGenerators_x, invertGenerators_y]
    dsimp [g, mirrorRelation]
    group
  have hp : applyHom invertGenerators (pair (square s k) (relation p s)) =
      pair (invertGenerators (square s k)) (invertGenerators (relation p s)) := by
    ext i
    fin_cases i <;> rfl
  rw [hp] at ht
  have h₁ := (inv_first (square s k) (mirrorRelation p s)).trans
    (conj_first (square s k)⁻¹ (mirrorRelation p s) (y ^ (-(s + k))))
  rw [ha] at h₁
  have h₂ := (inv_second (invertGenerators (square s k)) (mirrorRelation p s)).trans
    (conj_second (invertGenerators (square s k)) (mirrorRelation p s)⁻¹ g)
  rw [hb] at h₂
  exact h₁.trans (h₂.trans ht)

def rightShear (a : ℤ) : Word 2 →* Word 2 := FreeGroup.lift (pair (x * y ^ a) y)

@[simp] theorem rightShear_x (a : ℤ) : rightShear a x = x * y ^ a := by
  simp [rightShear, x, pair]

@[simp] theorem rightShear_y (a : ℤ) : rightShear a y = y := by
  simp [rightShear, y, pair]

theorem rightShear_standard (a : ℤ) :
    Reachable (applyHom (rightShear a) (standard 2)) (standard 2) := by
  have he : applyHom (rightShear a) (standard 2) = pair (x * y ^ a) y := by
    ext i
    fin_cases i <;> simp [applyHom, standard, rightShear, pair, x, y]
  rw [he]
  have h := (mulRight_zpow (pair (x * y ^ a) y) 0 1 (by decide) (-a)).reachable
  have hs : pair x y = standard 2 := by ext i; fin_cases i <;> rfl
  simpa [mul_assoc, hs] using h

/-- A single explicit occurrence of the second relator supplies the right pinch. -/
def rightPinchBase (a b : ℤ) :
    Witness (second a b 0) (x * y ^ b * x⁻¹) (y ^ (-a) * x) where
  factors := [(1, false)]
  sound := by
    simp only [product, Factor.value, Bool.false_eq_true, ↓reduceIte, mul_one,
      one_mul, inv_one]
    unfold second
    group

/-- The complementary pinch retains the same second relator as its donor. -/
def leftPinchBase (a b : ℤ) :
    Witness (second a b 0) (x⁻¹ * y ^ a * x) (x * y ^ (-b)) where
  factors := [((x * y ^ (-b))⁻¹, false)]
  sound := by
    simp only [product, Factor.value, Bool.false_eq_true, ↓reduceIte, mul_one]
    unfold second
    group

/-- A computed witness for every integer right divisibility quotient. -/
def rightPinchWitness (n : ℕ) (a b d : ℤ) (hn : (n + 1 : ℤ) = b * d) :
    Witness (second a b 0) (x * (first n)⁻¹ * x⁻¹)
      ((y ^ (-a) * x) ^ d * y ^ (-(n : ℤ))) :=
  (((rightPinchBase a b).zpow d).mul
    (Witness.refl (second a b 0) (y ^ (-(n : ℤ))))).change
      (by rw [conj_zpow, ← zpow_mul]; simp only [first, ← zpow_natCast, hn]; group) rfl

/-- A computed witness for every integer left divisibility quotient. -/
def leftPinchWitness (n : ℕ) (a b d : ℤ) (hn : (n : ℤ) = a * d) :
    Witness (second a b 0) (first n)
      ((x * y ^ (-b)) ^ d * y ^ (-(n + 1 : ℤ))) := by
  let w := ((leftPinchBase a b).zpow d).mul
    (Witness.refl (second a b 0) (y ^ (-(n + 1 : ℤ))))
  have he : (x⁻¹ * y ^ a * x) ^ d = x⁻¹ * y ^ (a * d) * x := by
    simpa only [inv_inv, ← zpow_mul] using
      (conj_zpow (i := d) (a := x⁻¹) (b := y ^ a))
  exact w.change (by rw [he]; simp only [first, ← zpow_natCast, hn]) rfl

/-- Each quotient unit contributes exactly one normal-closure factor. -/
theorem rightPinchWitness_length (n : ℕ) (a b d : ℤ) (hn : (n + 1 : ℤ) = b * d) :
    (rightPinchWitness n a b d hn).factors.length = d.natAbs := by
  simp [rightPinchWitness, rightPinchBase]

theorem leftPinchWitness_length (n : ℕ) (a b d : ℤ) (hn : (n : ℤ) = a * d) :
    (leftPinchWitness n a b d hn).factors.length = d.natAbs := by
  simp [leftPinchWitness, leftPinchBase]

/-- The right divisibility pinch reaches the exact power relator by ordinary moves. -/
theorem right_power_pinch (n : ℕ) (a b d : ℤ) (hn : (n + 1 : ℤ) = b * d) :
    Reachable (presentation n a b 0)
      (pair ((x * y ^ (-a)) ^ d * y ^ (-(n : ℤ))) (second a b 0)) := by
  let hw := rightPinchWitness n a b d hn
  have h₁ := (inv_first (first n) (second a b 0)).trans
    (conj_first (first n)⁻¹ (second a b 0) x)
  have h₂ := (replace (pair (x * (first n)⁻¹ * x⁻¹) (second a b 0))
    0 1 (by decide) hw.factors _ hw.sound).reachable
  simp only [pair_update_zero] at h₂
  have h₃ := conj_first ((y ^ (-a) * x) ^ d * y ^ (-(n : ℤ))) (second a b 0) (y ^ a)
  have he : y ^ a * ((y ^ (-a) * x) ^ d * y ^ (-(n : ℤ))) * (y ^ a)⁻¹ =
      (x * y ^ (-a)) ^ d * y ^ (-(n : ℤ)) := by
    calc
      _ = (y ^ a * (y ^ (-a) * x) ^ d * (y ^ a)⁻¹) * y ^ (-(n : ℤ)) := by group
      _ = (y ^ a * (y ^ (-a) * x) * (y ^ a)⁻¹) ^ d * y ^ (-(n : ℤ)) := by
        rw [conj_zpow]
      _ = _ := by congr 2; group
  rw [he] at h₃
  exact h₁.trans (h₂.trans h₃)

/-- The left divisibility pinch gives the complementary power relator. -/
theorem left_power_pinch (n : ℕ) (a b d : ℤ) (hn : (n : ℤ) = a * d) :
    Reachable (presentation n a b 0)
      (pair ((x * y ^ (-b)) ^ d * y ^ (-(n + 1 : ℤ))) (second a b 0)) := by
  let hw := leftPinchWitness n a b d hn
  have h := (replace (presentation n a b 0) 0 1 (by decide) hw.factors _ hw.sound).reachable
  simpa only [presentation, pair_update_zero] using h

/-- Quotient two on the right gives an exact square, for arbitrary first exponent. -/
theorem right_pinch (n : ℕ) (a b : ℤ) (hn : (n + 1 : ℤ) = 2 * b) :
    Reachable (presentation n a b 0)
      (pair ((x * y ^ (-a)) ^ 2 * y ^ (-(n : ℤ))) (second a b 0)) := by
  simpa only [zpow_ofNat] using right_power_pinch n a b 2 (by omega)

/-- Quotient two on the left gives the mirror square family. -/
theorem left_pinch (n : ℕ) (a b : ℤ) (hn : (n : ℤ) = 2 * a) :
    Reachable (presentation n a b 0)
      (pair ((x * y ^ (-b)) ^ 2 * y ^ (-(n + 1 : ℤ))) (second a b 0)) := by
  simpa only [zpow_ofNat] using left_power_pinch n a b 2 (by omega)

theorem odd_family (m : ℕ) (c : ℤ) :
    Reachable (presentation (2 * m + 1) 1 (m + 1) c) (standard 2) := by
  apply shear_family (2 * m + 1) 1 (m + 1) 0 _ c
  have ht := solvable_hom (rightShear (-1)) _ (odd_square_solvable m)
    (rightShear_standard (-1))
  have hp : applyHom (rightShear (-1)) (pair (square (m + 1) m) (relation 1 (m + 1))) =
      pair ((x * y ^ (-1 : ℤ)) ^ 2 * y ^ (-(2 * m + 1 : ℤ)))
        (x * (second 1 (m + 1) 0)⁻¹ * x⁻¹) := by
    ext i
    fin_cases i <;> simp [applyHom, pair, square, relation, second, pow_two] <;> group
  rw [hp] at ht
  have h := right_pinch (2 * m + 1) 1 (m + 1) (by omega)
  have h' := (inv_second ((x * y ^ (-1 : ℤ)) ^ 2 * y ^ (-(2 * m + 1 : ℤ)))
    (second 1 (m + 1) 0)).trans
      (conj_second ((x * y ^ (-1 : ℤ)) ^ 2 * y ^ (-(2 * m + 1 : ℤ)))
        (second 1 (m + 1) 0)⁻¹ x)
  have hc : ((2 * m + 1 : ℕ) : ℤ) = 2 * m + 1 := by omega
  rw [hc] at h
  exact h.trans (h'.trans ht)

theorem even_family (m : ℕ) (c : ℤ) :
    Reachable (presentation (2 * m) m 1 c) (standard 2) := by
  apply shear_family (2 * m) m 1 0 _ c
  have hmirror := mirror_solvable m (m + 1) 1 (even_square_solvable m)
  have ht := solvable_hom (rightShear (-1)) _ hmirror (rightShear_standard (-1))
  have hp : applyHom (rightShear (-1)) (pair (square m (m + 1)) (mirrorRelation 1 m)) =
      pair ((x * y ^ (-1 : ℤ)) ^ 2 * y ^ (-(2 * m + 1 : ℤ)))
        (x * (second m 1 0)⁻¹ * x⁻¹) := by
    ext i
    fin_cases i <;> simp [applyHom, pair, square, mirrorRelation, second, pow_two] <;> group
  rw [hp] at ht
  have h := left_pinch (2 * m) m 1 (by omega)
  have h' := (inv_second ((x * y ^ (-1 : ℤ)) ^ 2 * y ^ (-(2 * m + 1 : ℤ)))
    (second m 1 0)).trans
      (conj_second ((x * y ^ (-1 : ℤ)) ^ 2 * y ^ (-(2 * m + 1 : ℤ)))
        (second m 1 0)⁻¹ x)
  have hc : ((2 * m : ℕ) : ℤ) + 1 = 2 * m + 1 := by omega
  rw [hc] at h
  exact h.trans (h'.trans ht)

theorem odd_inverse_family (m : ℕ) (c : ℤ) :
    Reachable (presentation (2 * m + 1) (-1) (-(m + 1 : ℤ)) c) (standard 2) := by
  simpa only [neg_neg] using
    YInversion.solution (2 * m + 1) 1 (m + 1) (-c) (odd_family m (-c))

theorem even_inverse_family (m : ℕ) (c : ℤ) :
    Reachable (presentation (2 * m) (-(m : ℤ)) (-1) c) (standard 2) := by
  simpa only [neg_neg] using
    YInversion.solution (2 * m) m 1 (-c) (even_family m (-c))

end AC.MillerSchupp.SquareFamily
