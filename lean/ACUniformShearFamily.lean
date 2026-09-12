import ACDivisibility

/-!
# Uniform ordinary reductions for the observed Miller–Schupp shear family

The parameter-uniform family enters the published `w_star` family by four
ordinary moves. The latter is reduced using the proved divisibility construction
at exponent one. This supplies a formal proof, not a new-family priority claim.
-/

namespace AC.WordTransport

open AC.Certificate

/-- Reindex every relator and every affected slot in a supplied path. -/
theorem step_reindex {n : ℕ} (e : Equiv.Perm (Fin n)) {R S : Relators n}
    (h : Step R S) : Step (R ∘ e) (S ∘ e) := by
  have update_eq (R : Relators n) (i : Fin n) (w : Word n) :
      Function.update R i w ∘ e = Function.update (R ∘ e) (e.symm i) w := by
    simpa using Function.update_comp_eq_of_injective R e.injective (e.symm i) w
  cases h with
  | inv i =>
    simpa [update_eq, Function.comp_def] using Step.inv (R ∘ e) (e.symm i)
  | mulRight i j hij =>
    simpa [update_eq, Function.comp_def] using
      Step.mulRight (R ∘ e) (e.symm i) (e.symm j) (e.symm.injective.ne hij)
  | conj i w =>
    simpa [update_eq, Function.comp_def] using Step.conj (R ∘ e) (e.symm i) w

/-- Slot reindexing preserves the exact constructor count of a whole path. -/
theorem steps_reindex {n : ℕ} (e : Equiv.Perm (Fin n)) {R S : Relators n} {l : ℕ}
    (h : Steps R l S) : Steps (R ∘ e) l (S ∘ e) := by
  induction h with
  | refl => exact .refl _
  | tail _ step ih => exact ih.tail (step_reindex e step)

end AC.WordTransport

namespace AC.MillerSchupp.Uniform

open AC.Certificate AC.WordTransport AC.Substitution

/-- Swap generators in every word; this is used to transport a whole path. -/
def swapGenerators : Word 2 →* Word 2 := FreeGroup.lift (pair y x)

@[simp] theorem swapGenerators_x : swapGenerators x = y := by
  simp [swapGenerators, x, pair]

@[simp] theorem swapGenerators_y : swapGenerators y = x := by
  simp [swapGenerators, y, pair]

/-- Generator and relator swaps together preserve the ordered standard endpoint. -/
def swapBoth (R : Relators 2) : Relators 2 :=
  applyHom swapGenerators R ∘ Equiv.swap 0 1

@[simp] theorem swapBoth_pair (r q : Word 2) :
    swapBoth (pair r q) = pair (swapGenerators q) (swapGenerators r) := by
  ext i
  fin_cases i <;> simp [swapBoth, applyHom, pair]

@[simp] theorem swapBoth_standard : swapBoth (standard 2) = standard 2 := by
  ext i
  fin_cases i <;> simp [swapBoth, applyHom, standard, swapGenerators, pair, x, y]

/-- This transports each primitive; no free generator or relator move is inserted. -/
theorem swapBoth_steps {R S : Relators 2} {l : ℕ} (h : Steps R l S) :
    Steps (swapBoth R) l (swapBoth S) :=
  steps_reindex (Equiv.swap 0 1) (steps_hom swapGenerators h)

/-- A four-move bridge changes `a` by `n` while keeping `b` fixed. -/
theorem period_bridge_steps (n : ℕ) (a b : ℤ) :
    Steps (presentation n a b (-(n + 1 : ℤ))) 4
      (presentation n (a - (n : ℤ)) b 0) := by
  let r := first n
  let q := second a b (-(n + 1 : ℤ))
  let g := y ^ (-(n + 1 : ℤ))
  have h₁ : Step (pair r q) (pair r q⁻¹) := by
    simpa using Step.inv (pair r q) 1
  have h₂ : Step (pair r q⁻¹) (pair r (q⁻¹ * r)) := by
    simpa using Step.mulRight (pair r q⁻¹) 1 0 (by decide)
  have h₃ : Step (pair r (q⁻¹ * r)) (pair r (g * (q⁻¹ * r) * g⁻¹)) := by
    simpa using Step.conj (pair r (q⁻¹ * r)) 1 g
  have he : (g * (q⁻¹ * r) * g⁻¹)⁻¹ = second (a - (n : ℤ)) b 0 := by
    dsimp [r, q, g, first, second]
    group
  have h₄ : Step (pair r (g * (q⁻¹ * r) * g⁻¹))
      (pair r (second (a - (n : ℤ)) b 0)) := by
    simpa only [pair_one, he, pair_update_one] using
      Step.inv (pair r (g * (q⁻¹ * r) * g⁻¹)) 1
  exact (((Steps.single h₁).tail h₂).tail h₃).tail h₄

/-- The exponent-one input used in the published generator-interchange argument. -/
def coreWord (n : ℕ) : Word 2 := x ^ (-(n : ℤ)) * y⁻¹ * x ^ (n : ℤ) * y

theorem coreWord_eq_family (n : ℕ) :
    coreWord n = Divisibility.familyWord 1 0 [(n, -1), (0, 1)] := by
  simp [coreWord, Divisibility.familyWord, Divisibility.block]

theorem core_factorCount (n : ℕ) :
    Divisibility.factorCount 1 [(n, -1), (0, 1)] = 2 ^ n - 1 := by
  simp [Divisibility.factorCount, Divisibility.gap]

theorem core_totalExponent (n : ℕ) :
    Divisibility.totalExponent 1 [(n, -1), (0, 1)] = -(2 : ℤ) ^ n + 1 := by
  simp [Divisibility.totalExponent]

theorem core_exponent_abs (n : ℕ) : (-(2 : ℤ) ^ n + 1).natAbs = 2 ^ n - 1 := by
  have h : (2 : ℤ) ^ n = ((2 ^ n : ℕ) : ℤ) := by simp
  have hn : 1 ≤ (2 : ℕ) ^ n := by
    induction n with
    | zero => decide
    | succ n ih => rw [pow_succ]; omega
  rw [h]
  omega

/-- A fully constructed exponent-one solution, uniform in the natural exponent. -/
theorem core_counted (n : ℕ) :
    ∃ l ≤ 6 * (2 ^ n - 1) + 20,
      Steps (pair (first 1) (x⁻¹ * coreWord n)) l (standard 2) := by
  let ts : List Divisibility.Term := [(n, -1), (0, 1)]
  let fs := (Divisibility.familyWitness 1 0 ts).factors
  have hw : (x⁻¹ * coreWord n) * product (first 1) fs =
      x⁻¹ * (x ^ (0 : ℤ) * y ^ Divisibility.totalExponent 1 ts * x ^ (-(0 : ℤ))) := by
    rw [coreWord_eq_family]
    simpa only [mul_assoc] using
      congrArg (x⁻¹ * ·) (Divisibility.familyWitness_sound 1 0 ts)
  obtain ⟨l, hl, path⟩ := witnessed_power_conjugate_counted 1 0
    (Divisibility.totalExponent 1 ts) (coreWord n) fs hw
  have hc := (cost_bounds fs).2
  have hf : fs.length = 2 ^ n - 1 := by
    simpa only [fs, ts, Divisibility.familyWitness_length] using core_factorCount n
  have hb : (Divisibility.totalExponent 1 ts).natAbs = 2 ^ n - 1 := by
    simpa only [ts, core_totalExponent] using core_exponent_abs n
  rw [hf] at hc
  rw [hb] at hl
  exact ⟨l, by omega, path⟩

/-- The intermediate pair before swapping generators and slots in its whole solution. -/
def corePair (n : ℕ) : Relators 2 :=
  pair (first 1) (y⁻¹ * x ^ (n : ℤ) * y * x ^ (-(n + 1 : ℤ)))

theorem corePair_entry (n : ℕ) :
    Steps (corePair n) 1 (pair (first 1) (x⁻¹ * coreWord n)) := by
  have he : x ^ (-(n + 1 : ℤ)) *
      (y⁻¹ * x ^ (n : ℤ) * y * x ^ (-(n + 1 : ℤ))) *
      (x ^ (-(n + 1 : ℤ)))⁻¹ = x⁻¹ * coreWord n := by
    unfold coreWord
    group
  simpa only [corePair, pair_one, he, pair_update_one] using
    Steps.single (Step.conj (corePair n) 1 (x ^ (-(n + 1 : ℤ))))

theorem swapBoth_corePair (n : ℕ) :
    swapBoth (corePair n) = pair (first n) (y⁻¹ * x * y * x ^ (-2 : ℤ)) := by
  rw [corePair, swapBoth_pair]
  congr 1
  simp only [first, map_mul, map_inv, map_zpow, swapGenerators_x, swapGenerators_y]
  group

/-- Published `w_star` family, proved here from the constructed divisibility witness. -/
theorem star_counted (n : ℕ) :
    ∃ l ≤ 6 * (2 ^ n - 1) + 22,
      Steps (presentation n (-1) 1 0) l (standard 2) := by
  obtain ⟨l, hl, path⟩ := core_counted n
  have ht := swapBoth_steps ((corePair_entry n).trans path)
  rw [swapBoth_corePair, swapBoth_standard] at ht
  have he : x * second (-1) 1 0 * x⁻¹ = y⁻¹ * x * y * x ^ (-2 : ℤ) := by
    unfold second
    group
  have hp : Steps (presentation n (-1) 1 0) 1
      (pair (first n) (y⁻¹ * x * y * x ^ (-2 : ℤ))) := by
    simpa only [presentation, pair_one, he, pair_update_one] using
      Steps.single (Step.conj (presentation n (-1) 1 0) 1 x)
  exact ⟨_, by omega, hp.trans ht⟩

/-- The former two-seed pattern holds for every natural `n` and every integer `c`. -/
theorem uniform_family_counted (n : ℕ) (c : ℤ) :
    ∃ l ≤ 6 * (2 ^ n - 1) + 29 + (-(n + 1 : ℤ) - c).natAbs,
      Steps (presentation n ((n : ℤ) - 1) 1 c) l (standard 2) := by
  obtain ⟨l, hl, path⟩ := star_counted n
  have hp := period_bridge_steps n ((n : ℤ) - 1) 1
  have ha : (n : ℤ) - 1 - (n : ℤ) = -1 := by omega
  rw [ha] at hp
  obtain ⟨k, hk, result⟩ := shear_family_counted n ((n : ℤ) - 1) 1
    (-(n + 1 : ℤ)) (hp.trans path) c
  exact ⟨k, by omega, result⟩

theorem uniform_family (n : ℕ) (c : ℤ) :
    Reachable (presentation n ((n : ℤ) - 1) 1 c) (standard 2) := by
  obtain ⟨_, _, path⟩ := uniform_family_counted n c
  exact path.reachable

end AC.MillerSchupp.Uniform
