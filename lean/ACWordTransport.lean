import ACCertificate

/-!
# Whole-path substitution and integer relator powers

A word homomorphism transports each ordinary move. To transport a solution,
its image of the standard tuple must also be solved by actual ordinary moves.
-/

namespace AC.WordTransport

open AC.Certificate

variable {n : ℕ}

def applyHom (f : Word n →* Word n) (R : Relators n) : Relators n := fun i => f (R i)

theorem applyHom_update (f : Word n →* Word n) (R : Relators n)
    (i : Fin n) (w : Word n) :
    applyHom f (Function.update R i w) = Function.update (applyHom f R) i (f w) := by
  ext j
  by_cases hj : j = i
  · subst j; simp [applyHom]
  · simp [applyHom, hj]

theorem step_hom (f : Word n →* Word n) {R S : Relators n} (h : Step R S) :
    Step (applyHom f R) (applyHom f S) := by
  cases h with
  | inv i => simpa [applyHom_update, applyHom] using Step.inv (applyHom f R) i
  | mulRight i j hij =>
    simpa [applyHom_update, applyHom] using Step.mulRight (applyHom f R) i j hij
  | conj i w => simpa [applyHom_update, applyHom] using Step.conj (applyHom f R) i (f w)

/-- Substitution preserves the number of official primitives in a supplied path. -/
theorem steps_hom (f : Word n →* Word n) {R S : Relators n} {l : ℕ}
    (h : Steps R l S) : Steps (applyHom f R) l (applyHom f S) := by
  induction h with
  | refl => exact .refl _
  | tail _ step ih => exact ih.tail (step_hom f step)

theorem reachable_hom (f : Word n →* Word n) {R S : Relators n}
    (h : Reachable R S) : Reachable (applyHom f R) (applyHom f S) := by
  induction h with
  | refl => exact .refl _
  | tail _ step ih => exact ih.trans (.single (step_hom f step))

/-- The endpoint obligation prevents arbitrary substitution from being treated as a free move. -/
theorem solvable_hom (f : Word n →* Word n) (R : Relators n)
    (h : Reachable R (standard n)) (hf : Reachable (applyHom f (standard n)) (standard n)) :
    Reachable (applyHom f R) (standard n) := (reachable_hom f h).trans hf

theorem mulRight_pow (R : Relators n) (i j : Fin n) (hij : i ≠ j) (m : ℕ) :
    Steps R m (Function.update R i (R i * R j ^ m)) := by
  induction m with
  | zero => simpa using Steps.refl R
  | succ m ih =>
    let S := Function.update R i (R i * R j ^ m)
    have h := ih.tail (Step.mulRight S i j hij)
    simpa [S, hij.symm, pow_succ, mul_assoc] using h

/-- A negative power needs two additional inversions, with the source restored. -/
theorem mulRight_zpow (R : Relators n) (i j : Fin n) (hij : i ≠ j) (m : ℤ) :
    Steps R (m.natAbs + if m < 0 then 2 else 0)
      (Function.update R i (R i * R j ^ m)) := by
  cases m with
  | ofNat m => simpa using mulRight_pow R i j hij m
  | negSucc m =>
    let S := Function.update R j (R j)⁻¹
    let T := Function.update S i (S i * S j ^ (m + 1))
    have h := ((Steps.single (Step.inv R j)).trans
      (mulRight_pow S i j hij (m + 1))).tail (Step.inv T j)
    have ht : Function.update T j (T j)⁻¹ =
        Function.update R i (R i * R j ^ (Int.negSucc m)) := by
      ext a
      by_cases hai : a = i
      · subst a; simp [T, S, hij, hij.symm, zpow_negSucc, inv_pow]
      · by_cases haj : a = j
        · subst a; simp [T, S, hij, hij.symm]
        · simp [T, S, hai, haj]
    rw [ht] at h
    convert h using 1
    simp
    omega

end AC.WordTransport
