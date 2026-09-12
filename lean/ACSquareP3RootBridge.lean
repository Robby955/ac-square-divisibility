import ACSquareP3Families

/-! A counted uniform root-degree reduction for the remaining degree-three slice. -/

namespace AC.MillerSchupp.SquareFamily.Residual
open AC.Certificate AC.Substitution AC.WordTransport

/-- The changed companion is outside the previously solved two-block companion family. -/
def twoRootCompanion (d : ℤ) : Word 2 :=
  y⁻¹ * x⁻¹ * y⁻¹ * x⁻¹ * y * x ^ (-d)

def bridgeMap : Word 2 →* Word 2 := FreeGroup.lift (pair x (y * x⁻¹))
def bridgeInverse : Word 2 →* Word 2 := FreeGroup.lift (pair x (y * x))

@[simp] theorem bridgeMap_x : bridgeMap x = x := by simp [bridgeMap, pair, x]
@[simp] theorem bridgeMap_y : bridgeMap y = y * x⁻¹ := by simp [bridgeMap, pair, y]
@[simp] theorem bridgeInverse_x : bridgeInverse x = x := by simp [bridgeInverse, pair, x]
@[simp] theorem bridgeInverse_y : bridgeInverse y = y * x := by simp [bridgeInverse, pair, y]

def bridgeFactors : List (Factor 2) :=
  [(x * y ^ (-3 : ℤ) * x ^ (-2 : ℤ) * y ^ (3 : ℤ), false), (x, true)]

/-- Only two supplied conjugates of the companion are needed. -/
theorem bridge_factor_identity (d : ℤ) :
    P2.root 3 * product (relation 1 d) bridgeFactors =
    x ^ (d - 1) * bridgeMap (P2.root 2) * (x ^ (d - 1))⁻¹ := by
  simp [P2.root, relation, product, bridgeFactors, Factor.value]
  simp only [zpow_ofNat, pow_two, mul_inv_rev, inv_inv]
  group

/-- Ten arbitrary-word mathematical primitives, with the donor restored. -/
theorem root_three_to_two (d : ℤ) :
    Steps (pair (P2.root 3) (relation 1 d)) 10
      (applyHom bridgeMap (pair (P2.root 2) (twoRootCompanion d))) := by
  have h₁ := replace (pair (P2.root 3) (relation 1 d)) 0 1 (by decide)
    bridgeFactors _ (bridge_factor_identity d)
  have hcost : cost bridgeFactors = 8 := rfl
  simp only [hcost, pair_update_zero] at h₁
  have h₂ := Steps.single (Step.conj
    (pair (x ^ (d - 1) * bridgeMap (P2.root 2) * (x ^ (d - 1))⁻¹)
      (relation 1 d)) 0 (x ^ (1 - d)))
  have he : x ^ (1 - d) *
      (x ^ (d - 1) * bridgeMap (P2.root 2) * (x ^ (d - 1))⁻¹) *
      (x ^ (1 - d))⁻¹ = bridgeMap (P2.root 2) := by group
  simp only [pair_zero, he, pair_update_zero] at h₂
  have h₃ := Steps.single (Step.conj
    (pair (bridgeMap (P2.root 2)) (relation 1 d)) 1 x)
  have he : x * relation 1 d * x⁻¹ = bridgeMap (twoRootCompanion d) := by
    simp [relation, twoRootCompanion]
    group
  simp only [pair_one, he, pair_update_one] at h₃
  have hp : pair (bridgeMap (P2.root 2)) (bridgeMap (twoRootCompanion d)) =
      applyHom bridgeMap (pair (P2.root 2) (twoRootCompanion d)) := by
    ext i; fin_cases i <;> simp [applyHom]
  simpa only [hp] using (h₁.trans h₂).trans h₃

theorem bridgeMap_standard : Reachable (applyHom bridgeMap (standard 2)) (standard 2) := by
  have hp : applyHom bridgeMap (standard 2) = pair x (y * x⁻¹) := by
    ext i; fin_cases i <;> simp [applyHom, standard, pair, x, y, bridgeMap]
  rw [hp]
  have h := Reachable.single (Step.mulRight (pair x (y * x⁻¹)) 1 0 (by decide))
  have he : pair x y = standard 2 := by ext i; fin_cases i <;> rfl
  simpa only [pair_zero, pair_one, mul_assoc, inv_mul_cancel, mul_one, pair_update_one, he] using h

theorem bridgeInverse_standard :
    Reachable (applyHom bridgeInverse (standard 2)) (standard 2) := by
  have hp : applyHom bridgeInverse (standard 2) = pair x (y * x) := by
    ext i; fin_cases i <;> simp [applyHom, standard, pair, x, y, bridgeInverse]
  rw [hp]
  have h := (Steps.mulInvRight (pair x (y * x)) 1 0 (by decide)).reachable
  have he : pair x y = standard 2 := by ext i; fin_cases i <;> rfl
  simpa only [pair_zero, pair_one, mul_assoc, mul_inv_cancel, mul_one, pair_update_one, he] using h

/-- Both directions have explicit ordinary paths, including the basis endpoints. -/
theorem root_three_two_iff (d : ℤ) :
    Reachable (pair (P2.root 3) (relation 1 d)) (standard 2) ↔
    Reachable (pair (P2.root 2) (twoRootCompanion d)) (standard 2) := by
  constructor
  · intro h
    have ht := (ResidueClasses.reverse_path (root_three_to_two d).reachable).trans h
    have hi := solvable_hom bridgeInverse _ ht bridgeInverse_standard
    have he : applyHom bridgeInverse
        (applyHom bridgeMap (pair (P2.root 2) (twoRootCompanion d))) =
        pair (P2.root 2) (twoRootCompanion d) := by
      ext i; fin_cases i <;> simp [applyHom, pair, P2.root, twoRootCompanion, mul_assoc]
    rwa [he] at hi
  · intro h
    exact (root_three_to_two d).reachable.trans (solvable_hom bridgeMap _ h bridgeMap_standard)

/-- The precise square-family target is equivalent to this changed degree-two companion. -/
theorem degree_three_two_root_iff (m : ℕ) :
    Reachable (Diagonal.generalSquare 3 (3 * m + 1)) (standard 2) ↔
    Reachable (pair (P2.root 2) (twoRootCompanion ((2 : ℤ) ^ m))) (standard 2) :=
  (degree_three_iff m).trans (root_three_two_iff ((2 : ℤ) ^ m))

end AC.MillerSchupp.SquareFamily.Residual
