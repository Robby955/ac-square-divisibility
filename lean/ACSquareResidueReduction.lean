import ACSquareP2Families

/-! Exact residual interface for the remaining square-family parameters. -/

namespace AC.MillerSchupp.SquareFamily.Residual
open AC.Certificate AC.Substitution AC.WordTransport

def relation (r d : ℤ) : Word 2 := y ^ (-(r + 1)) * x⁻¹ * y ^ r * x ^ (-d)

/-- The finite doubling witness retains the remainder of the companion height. -/
def reductionWitness (p r : ℤ) (m : ℕ) :
    Witness (P2.root p)
      (y ^ (p * m) * P2.companion (p * m + r) * (y ^ (p * m))⁻¹)
      (relation r ((2 : ℤ) ^ m)) := by
  let a := (Witness.refl (P2.root p) (y⁻¹ * (y ^ (-r) * x⁻¹ * y ^ r))).mul
    (P2.iteratedDouble p m).inverse
  exact a.change (by dsimp [P2.companion]; group)
    (by dsimp [relation]; simp only [← zpow_natCast, Nat.cast_pow, Nat.cast_ofNat]; group)

theorem root_to_residual (p r : ℤ) (m : ℕ) :
    Reachable (pair (P2.root p) (P2.companion (p * m + r)))
      (pair (P2.root p) (relation r ((2 : ℤ) ^ m))) := by
  let w := reductionWitness p r m
  have hc := Reachable.single (Step.conj
    (pair (P2.root p) (P2.companion (p * m + r))) 1 (y ^ (p * (m : ℤ))))
  simp only [pair_one, pair_update_one] at hc
  have hw := (replace (pair (P2.root p)
      (y ^ (p * m) * P2.companion (p * m + r) * (y ^ (p * m))⁻¹))
    1 0 (by decide) w.factors _ w.sound).reachable
  simp only [pair_update_one] at hw
  exact hc.trans hw

def inverseEntryMap (p s : ℤ) : Word 2 →* Word 2 :=
  FreeGroup.lift (pair (y ^ (-p) * x⁻¹ * y ^ (p - s - 1)) y⁻¹)

@[simp] theorem inverseEntryMap_x (p s : ℤ) :
    inverseEntryMap p s x = y ^ (-p) * x⁻¹ * y ^ (p - s - 1) := by
  simp [inverseEntryMap, pair, x]

@[simp] theorem inverseEntryMap_y (p s : ℤ) : inverseEntryMap p s y = y⁻¹ := by
  simp [inverseEntryMap, pair, y]

/-- The inverse basis map also has a supplied ordinary standard endpoint. -/
theorem inverseEntryMap_standard (p s : ℤ) :
    Reachable (applyHom (inverseEntryMap p s) (standard 2)) (standard 2) := by
  have he : inverseEntryMap p s = P2.entryMap (p - s - 1) (-s - 2) := by
    simp only [inverseEntryMap, P2.entryMap,
      show -s - 2 + 1 - (p - s - 1) = -p by ring]
  rw [he]
  exact P2.entryMap_standard (p - s - 1) (-s - 2)

theorem inverseEntryMap_pair (p s : ℤ) :
    applyHom (inverseEntryMap p s)
      (applyHom (P2.entryMap p s) (pair (P2.root p) (P2.companion s))) =
      pair (P2.root p) (P2.companion s) := by
  ext i
  fin_cases i <;> simp [applyHom, pair, P2.root, P2.companion, pow_two] <;> group

/-- Both directions use ordinary paths with supplied basis corrections. -/
theorem square_root_iff (p s : ℤ) :
    Reachable (Diagonal.generalSquare p s) (standard 2) ↔
      Reachable (pair (P2.root p) (P2.companion s)) (standard 2) := by
  constructor
  · intro h
    have he := (Diagonal.general_normal_form p s).reachable.trans (P2.root_entry p s).reachable
    have ht := (ResidueClasses.reverse_path he).trans h
    have hi := solvable_hom (inverseEntryMap p s) _ ht (inverseEntryMap_standard p s)
    rwa [inverseEntryMap_pair] at hi
  · exact P2.square_of_root p s

/-- The residual formulation is equivalent to the original square tuple. -/
theorem square_residual_iff (p r : ℤ) (m : ℕ) :
    Reachable (Diagonal.generalSquare p (p * m + r)) (standard 2) ↔
      Reachable (pair (P2.root p) (relation r ((2 : ℤ) ^ m))) (standard 2) :=
  (square_root_iff p (p * m + r)).trans
    (ResidueClasses.path_solvable_iff (root_to_residual p r m))

/-- Exact degree-three interface for the unresolved slice. -/
theorem degree_three_iff (m : ℕ) :
    Reachable (Diagonal.generalSquare 3 (3 * m + 1)) (standard 2) ↔
      Reachable (pair (P2.root 3) (relation 1 ((2 : ℤ) ^ m))) (standard 2) :=
  square_residual_iff 3 1 m

/-- The zero-index residual seed follows from previously solved square residues. -/
theorem degree_three_base :
    Reachable (pair (P2.root 3) (relation 1 1)) (standard 2) := by
  apply (degree_three_iff 0).mp
  apply P2.covered_positive 1 3
  exact ⟨0, 1, by norm_num, Or.inl rfl⟩

end AC.MillerSchupp.SquareFamily.Residual
