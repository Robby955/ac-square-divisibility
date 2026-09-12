import ACCertificate

/-!
# Counted substitution from explicit normal-closure witnesses

Each factor is a conjugating word and a Boolean sign: `true` means the source
relator, and `false` means its inverse. The source is a distinct relator slot
and is restored after every factor. Conjugations use the official arbitrary-word
constructor, so these counts do not assert generator-only numbered move costs.
-/

namespace AC.Substitution

open AC.Certificate

variable {n : ℕ}

/-- A conjugating word and a sign, with `true` positive and `false` negative. -/
abbrev Factor (n : ℕ) := Word n × Bool

def Factor.value (r : Word n) (f : Factor n) : Word n :=
  f.1 * (if f.2 then r else r⁻¹) * f.1⁻¹

def Factor.cost (f : Factor n) : ℕ := if f.2 then 3 else 5

/-- Ordered product of conjugates of one fixed source relator. -/
def product (r : Word n) : List (Factor n) → Word n
  | [] => 1
  | f :: fs => f.value r * product r fs

/-- Exact count of the constructed path, including restoration of the source. -/
def cost : List (Factor n) → ℕ
  | [] => 0
  | f :: fs => f.cost + cost fs

theorem mulConjugate (R : Relators n) (i j : Fin n) (hij : i ≠ j) (g : Word n) :
    Steps R 3 (Function.update R i (R i * (g * R j * g⁻¹))) := by
  let R₁ := Function.update R j (g * R j * g⁻¹)
  let R₂ := Function.update R₁ i (R₁ i * R₁ j)
  let R₃ := Function.update R₂ j (g⁻¹ * R₂ j * (g⁻¹)⁻¹)
  have heq : R₃ = Function.update R i (R i * (g * R j * g⁻¹)) := by
    ext k
    by_cases hki : k = i
    · subst k; simp [R₃, R₂, R₁, hij, hij.symm]
    · by_cases hkj : k = j
      · subst k; simp [R₃, R₂, R₁, hij, hij.symm, mul_assoc]
      · simp [R₃, R₂, R₁, hki, hkj]
  rw [← heq]
  exact ((Steps.single (Step.conj R j g)).tail (Step.mulRight R₁ i j hij)).tail
    (Step.conj R₂ j g⁻¹)

theorem mulConjugateInv (R : Relators n) (i j : Fin n) (hij : i ≠ j) (g : Word n) :
    Steps R 5 (Function.update R i (R i * (g * (R j)⁻¹ * g⁻¹))) := by
  let R₁ := Function.update R j (g * R j * g⁻¹)
  let R₂ := Function.update R₁ i (R₁ i * (R₁ j)⁻¹)
  let R₃ := Function.update R₂ j (g⁻¹ * R₂ j * (g⁻¹)⁻¹)
  have heq : R₃ = Function.update R i (R i * (g * (R j)⁻¹ * g⁻¹)) := by
    ext k
    by_cases hki : k = i
    · subst k; simp [R₃, R₂, R₁, hij, hij.symm, mul_assoc]
    · by_cases hkj : k = j
      · subst k; simp [R₃, R₂, R₁, hij, hij.symm, mul_assoc]
      · simp [R₃, R₂, R₁, hki, hkj]
  rw [← heq]
  exact ((Steps.single (Step.conj R j g)).trans (Steps.mulInvRight R₁ i j hij)).tail
    (Step.conj R₂ j g⁻¹)

/-- One witnessed factor is compiled to three or five official primitives. -/
theorem mulFactor (R : Relators n) (i j : Fin n) (hij : i ≠ j) (f : Factor n) :
    Steps R f.cost (Function.update R i (R i * f.value (R j))) := by
  rcases f with ⟨g, sign⟩
  cases sign with
  | false => simpa [Factor.cost, Factor.value] using mulConjugateInv R i j hij g
  | true => simpa [Factor.cost, Factor.value] using mulConjugate R i j hij g

/-- Compile an ordered finite normal-closure witness, restoring all other slots. -/
theorem mulProduct (R : Relators n) (i j : Fin n) (hij : i ≠ j)
    (fs : List (Factor n)) :
    Steps R (cost fs) (Function.update R i (R i * product (R j) fs)) := by
  induction fs generalizing R with
  | nil => simpa [cost, product] using Steps.refl R
  | cons f fs ih =>
    let S := Function.update R i (R i * f.value (R j))
    have first : Steps R f.cost S := mulFactor R i j hij f
    have rest := ih S
    simpa [S, cost, product, hij.symm, mul_assoc] using first.trans rest

/-- Replace one relator using an exact free-group equality, not an oracle. -/
theorem replace (R : Relators n) (i j : Fin n) (hij : i ≠ j)
    (fs : List (Factor n)) (target : Word n)
    (witness : R i * product (R j) fs = target) :
    Steps R (cost fs) (Function.update R i target) := by
  rw [← witness]
  exact mulProduct R i j hij fs

theorem cost_bounds (fs : List (Factor n)) :
    3 * fs.length ≤ cost fs ∧ cost fs ≤ 5 * fs.length := by
  induction fs with
  | nil => simp [cost]
  | cons f fs ih =>
    simp only [cost, List.length_cons, Factor.cost]
    split <;> omega

end AC.Substitution
