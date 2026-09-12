import AC
import Mathlib.GroupTheory.Perm.Sign

/-!
# Deletion deferral for the official Andrews–Curtis definitions

Ordinary moves lift through insertion of an isolated generator–relator pair.
This gives a reduction of paths with no additions to ordinary reachability.
Neither universal conjecture is assumed or established here.
-/

namespace AC

variable {n : ℕ}

@[simp] theorem stabilize_at (R : Relators n) (g i : Fin (n + 1)) :
    stabilize R g i i = FreeGroup.of g := by
  simp [stabilize]

@[simp] theorem stabilize_succAbove (R : Relators n) (g i : Fin (n + 1))
    (j : Fin n) :
    stabilize R g i (i.succAbove j) = FreeGroup.map g.succAbove (R j) := by
  simp [stabilize]

theorem stabilize_update (R : Relators n) (g i : Fin (n + 1)) (j : Fin n)
    (w : Word n) :
    stabilize (Function.update R j w) g i =
      Function.update (stabilize R g i) (i.succAbove j) (FreeGroup.map g.succAbove w) := by
  ext k
  induction k using i.succAboveCases
  · simp
  · rename_i k
    by_cases h : k = j
    · subst k; simp
    · simp [h]

/-- An ordinary move lifts through any independent generator and relator insertion positions. -/
theorem Step.stabilize {R S : Relators n} (h : Step R S) (g i : Fin (n + 1)) :
    Step (AC.stabilize R g i) (AC.stabilize S g i) := by
  cases h with
  | inv j =>
    simpa [stabilize_update] using Step.inv (AC.stabilize R g i) (i.succAbove j)
  | mulRight j k hjk =>
    have hne : i.succAbove j ≠ i.succAbove k := Fin.succAbove_right_injective.ne hjk
    simpa [stabilize_update] using Step.mulRight (AC.stabilize R g i) _ _ hne
  | conj j w =>
    simpa [stabilize_update] using
      Step.conj (AC.stabilize R g i) (i.succAbove j) (FreeGroup.map g.succAbove w)

theorem Reachable.refl (R : Relators n) : Reachable R R :=
  Relation.ReflTransGen.refl

theorem Reachable.single {R S : Relators n} (h : Step R S) : Reachable R S :=
  Relation.ReflTransGen.single h

theorem Reachable.trans {R S T : Relators n} (h : Reachable R S) (h' : Reachable S T) :
    Reachable R T := Relation.ReflTransGen.trans h h'

/-- A finite ordinary path lifts while leaving the inserted pair isolated. -/
theorem Reachable.stabilize {R S : Relators n} (h : Reachable R S)
    (g i : Fin (n + 1)) : Reachable (AC.stabilize R g i) (AC.stabilize S g i) := by
  induction h with
  | refl => exact .refl _
  | tail h step ih => exact Relation.ReflTransGen.tail ih (step.stabilize g i)

/-- Swapping two relators is realized by seven official ordinary moves. -/
theorem Reachable.swap (R : Relators n) (i j : Fin n) (hij : i ≠ j) :
    Reachable R (R ∘ Equiv.swap i j) := by
  let R₁ := Function.update R i (R i * R j)
  let R₂ := Function.update R₁ i (R₁ i)⁻¹
  let R₃ := Function.update R₂ j (R₂ j * R₂ i)
  let R₄ := Function.update R₃ i (R₃ i)⁻¹
  let R₅ := Function.update R₄ i ((R i)⁻¹ * R₄ i * ((R i)⁻¹)⁻¹)
  let R₆ := Function.update R₅ i (R₅ i * R₅ j)
  let R₇ := Function.update R₆ j (R₆ j)⁻¹
  have h₁ : Step R R₁ := .mulRight R i j hij
  have h₂ : Step R₁ R₂ := .inv R₁ i
  have h₃ : Step R₂ R₃ := .mulRight R₂ j i hij.symm
  have h₄ : Step R₃ R₄ := .inv R₃ i
  have h₅ : Step R₄ R₅ := .conj R₄ i (R i)⁻¹
  have h₆ : Step R₅ R₆ := .mulRight R₅ i j hij
  have h₇ : Step R₆ R₇ := .inv R₆ j
  have end_eq : R₇ = R ∘ Equiv.swap i j := by
    ext k
    by_cases hki : k = i
    · subst k
      simp [R₇, R₆, R₅, R₄, R₃, R₂, R₁, hij, hij.symm, mul_assoc]
    · by_cases hkj : k = j
      · subst k
        simp [R₇, R₆, R₅, R₄, R₃, R₂, R₁, hij, hij.symm, mul_assoc]
      · simp [R₇, R₆, R₅, R₄, R₃, R₂, R₁, hki, hkj,
              Equiv.swap_apply_of_ne_of_ne hki hkj]
  rw [← end_eq]
  exact ((((((Reachable.single h₁).trans (.single h₂)).trans (.single h₃)).trans
    (.single h₄)).trans (.single h₅)).trans (.single h₆)).trans (.single h₇)

/-- Every relator permutation is charged through ordinary move paths. -/
theorem Reachable.permute (R : Relators n) (σ : Equiv.Perm (Fin n)) :
    Reachable R (R ∘ σ) := by
  induction σ using Equiv.Perm.swap_induction_on' with
  | one => simpa using Reachable.refl R
  | mul_swap σ i j hij ih =>
    exact ih.trans (Reachable.swap (R ∘ σ) i j hij)

theorem permuted_standard_reachable (σ : Equiv.Perm (Fin n)) :
    Reachable (fun j => FreeGroup.of (σ j)) (standard n) := by
  simpa [Function.comp_def, standard] using
    Reachable.permute (fun j => FreeGroup.of (σ j)) σ.symm

/-- The singleton permutation created by arbitrary independent insertion positions. -/
def insertionPerm (g i : Fin (n + 1)) : Equiv.Perm (Fin (n + 1)) where
  toFun := Fin.insertNth i g g.succAbove
  invFun := Fin.insertNth g i i.succAbove
  left_inv k := by
    induction k using i.succAboveCases <;> simp
  right_inv k := by
    induction k using g.succAboveCases <;> simp

theorem stabilize_standard_reachable (g i : Fin (n + 1)) :
    Reachable (stabilize (standard n) g i) (standard (n + 1)) := by
  have h : stabilize (standard n) g i = fun j => FreeGroup.of (insertionPerm g i j) := by
    ext k
    induction k using i.succAboveCases <;> simp [insertionPerm, standard]
  rw [h]
  exact permuted_standard_reachable _

/-- Stable moves restricted to ordinary moves and deletion of an isolated positive pair. -/
inductive NoAddStep : Presentation → Presentation → Prop
  | ac {n : ℕ} {R S : Relators n} (h : Step R S) : NoAddStep ⟨n, R⟩ ⟨n, S⟩
  | destabilize {n : ℕ} (R : Relators n) (g i : Fin (n + 1)) :
      NoAddStep ⟨n + 1, stabilize R g i⟩ ⟨n, R⟩

/-- A finite path with no additions. -/
def NoAddReachable : Presentation → Presentation → Prop :=
  Relation.ReflTransGen NoAddStep

theorem NoAddStep.toStable {P Q : Presentation} (h : NoAddStep P Q) : StableStep P Q := by
  cases h with
  | ac h => exact .ac h
  | destabilize R g i => exact .destabilize R g i

theorem NoAddReachable.toStable {P Q : Presentation} (h : NoAddReachable P Q) :
    StableReachable P Q := by
  induction h with
  | refl => exact .refl
  | tail h step ih => exact ih.tail step.toStable

private theorem noAddStep_prepend {P Q : Presentation} (h : NoAddStep P Q)
    (hq : Reachable Q.2 (standard Q.1)) : Reachable P.2 (standard P.1) := by
  cases h with
  | ac h => exact (Reachable.single h).trans hq
  | destabilize R g i => exact (hq.stabilize g i).trans (stabilize_standard_reachable g i)

/-- A no-additions prefix preserves ordinary solvability backwards. -/
theorem NoAddReachable.prepend {P Q : Presentation} (h : NoAddReachable P Q) :
    Reachable Q.2 (standard Q.1) → Reachable P.2 (standard P.1) := by
  induction h with
  | refl => exact id
  | tail h step ih => exact fun hq => ih (noAddStep_prepend step hq)

/-- Deletion deferral at every finite rank, including zero; no group hypothesis is needed. -/
theorem noAdd_to_empty_implies_ordinary (R : Relators n)
    (h : NoAddReachable ⟨n, R⟩ ⟨0, standard 0⟩) : Reachable R (standard n) :=
  h.prepend (Reachable.refl _)

/-- Inserting the matching standard pair at the same positions leaves the standard tuple. -/
@[simp] theorem stabilize_standard_same (i : Fin (n + 1)) :
    stabilize (standard n) i i = standard (n + 1) := by
  ext k
  induction k using i.succAboveCases <;> simp [standard]

theorem NoAddReachable.ofOrdinary {R S : Relators n} (h : Reachable R S) :
    NoAddReachable ⟨n, R⟩ ⟨n, S⟩ := by
  induction h with
  | refl => exact .refl
  | tail h step ih => exact ih.tail (.ac step)

/-- Standard tuples reduce to empty by deleting isolated positive pairs. -/
theorem NoAddReachable.standard_to_empty (n : ℕ) :
    NoAddReachable ⟨n, standard n⟩ ⟨0, standard 0⟩ := by
  induction n with
  | zero => exact .refl
  | succ n ih =>
    have first : NoAddStep ⟨n + 1, standard (n + 1)⟩ ⟨n, standard n⟩ := by
      simpa using NoAddStep.destabilize (standard n) (Fin.last n) (Fin.last n)
    exact (Relation.ReflTransGen.single first).trans ih

/-- Ordinary solvability is equivalent to stable solvability with no generator additions. -/
theorem noAdd_to_empty_iff_ordinary (R : Relators n) :
    NoAddReachable ⟨n, R⟩ ⟨0, standard 0⟩ ↔ Reachable R (standard n) := by
  constructor
  · exact noAdd_to_empty_implies_ordinary R
  · intro h
    exact (NoAddReachable.ofOrdinary h).trans (NoAddReachable.standard_to_empty n)

end AC
