import ACWitness
import ACMillerSchuppCounted
import Mathlib.Algebra.Group.Conj
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Constructed witnesses for the common-height divisibility family

Each block is parameterized by a natural deficit `d` below an integer common
height `H`, and an arbitrary integer coefficient `c`. All factor lists are
defined recursively, with proofs of their identities and exact lengths.
-/

namespace AC.MillerSchupp.Divisibility

open AC.Substitution AC.Certificate

/-- One occurrence of the defining Baumslag–Solitar relation, in the raising direction. -/
def riseBase (n : ℕ) : Witness (first n) (y ^ (n : ℤ))
    (x * y ^ (n + 1 : ℤ) * x⁻¹) where
  factors := [(x * y ^ (-(n + 1 : ℤ)), false)]
  sound := by
    simp only [product, Factor.value, Bool.false_eq_true, ↓reduceIte, mul_one, first]
    group

/-- Raise one level, including negative and zero coefficients. -/
def riseOne (n : ℕ) (c : ℤ) : Witness (first n) (y ^ ((n : ℤ) * c))
    (x * y ^ ((n + 1 : ℤ) * c) * x⁻¹) :=
  ((riseBase n).zpow c).change (by rw [← zpow_mul]) (by rw [conj_zpow, ← zpow_mul])

@[simp] theorem riseOne_length (n : ℕ) (c : ℤ) :
    (riseOne n c).factors.length = c.natAbs := by
  simp [riseOne, riseBase]

/-- Raise a power through `d` levels, retaining every normal-closure factor. -/
def rise (n : ℕ) : (d : ℕ) → (c : ℤ) →
    Witness (first n) (y ^ ((n : ℤ) ^ d * c))
      (x ^ (d : ℤ) * y ^ ((n + 1 : ℤ) ^ d * c) * x ^ (-(d : ℤ)))
  | 0, c => Witness.ofEq (first n) (by simp)
  | d + 1, c =>
    let s := riseOne n ((n : ℤ) ^ d * c)
    let t := (rise n d ((n + 1 : ℤ) * c)).conj x
    let s' := s.change rfl (show x * y ^ ((n + 1 : ℤ) * ((n : ℤ) ^ d * c)) * x⁻¹ =
        x * y ^ ((n : ℤ) ^ d * ((n + 1 : ℤ) * c)) * x⁻¹ by
      rw [show (n + 1 : ℤ) * ((n : ℤ) ^ d * c) =
        (n : ℤ) ^ d * ((n + 1 : ℤ) * c) by ring])
    (s'.trans t).change
      (by congr 1; rw [pow_succ]; ring)
      (by
        rw [show (n + 1 : ℤ) ^ d * ((n + 1 : ℤ) * c) =
          (n + 1 : ℤ) ^ (d + 1) * c by rw [pow_succ]; ring]
        group)

/-- The telescoping geometric factor in the exact witness length. -/
def gap (n d : ℕ) : ℕ := (n + 1) ^ d - n ^ d

@[simp] theorem gap_zero (n : ℕ) : gap n 0 = 0 := by simp [gap]

theorem gap_succ (n d : ℕ) : gap n (d + 1) = n ^ d + (n + 1) * gap n d := by
  have h : n ^ d ≤ (n + 1) ^ d := Nat.pow_le_pow_left (Nat.le_succ n) d
  have he := congrArg (fun a => (n + 1) * a) (Nat.sub_add_cancel h)
  have hs : (n + 1) ^ d * (n + 1) =
      n ^ d * n + (n ^ d + (n + 1) * ((n + 1) ^ d - n ^ d)) := by
    nlinarith [he]
  unfold gap
  rw [pow_succ, pow_succ]
  omega

/-- No asymptotic estimate is used: this is the exact length of the constructed list. -/
theorem rise_length (n d : ℕ) (c : ℤ) :
    (rise n d c).factors.length = c.natAbs * gap n d := by
  induction d generalizing c with
  | zero => simp [rise, Witness.ofEq]
  | succ d ih =>
    have hn : (n + 1 : ℤ).natAbs = n + 1 := by omega
    simp only [rise, Witness.factors_change, Witness.length_trans, Witness.length_conj,
      riseOne_length, ih, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast, hn, gap_succ]
    ring

def block (n : ℕ) (H : ℤ) (d : ℕ) (c : ℤ) : Word 2 :=
  x ^ (H - d) * y ^ ((n : ℤ) ^ d * c) * x ^ (-(H - d))

/-- Move a block from its original height `H-d` to the chosen common height. -/
def blockWitness (n : ℕ) (H : ℤ) (d : ℕ) (c : ℤ) :
    Witness (first n) (block n H d c)
      (x ^ H * y ^ ((n + 1 : ℤ) ^ d * c) * x ^ (-H)) :=
  ((rise n d c).conj (x ^ (H - d))).change
    (by simp only [block, zpow_neg]) (by group)

@[simp] theorem blockWitness_length (n : ℕ) (H : ℤ) (d : ℕ) (c : ℤ) :
    (blockWitness n H d c).factors.length = c.natAbs * gap n d := by
  simp [blockWitness, rise_length]

/-- Natural deficits encode precisely the requirement that every original height is at most `H`. -/
abbrev Term := ℕ × ℤ

def familyWord (n : ℕ) (H : ℤ) : List Term → Word 2
  | [] => 1
  | (d, c) :: ts => block n H d c * familyWord n H ts

def totalExponent (n : ℕ) : List Term → ℤ
  | [] => 0
  | (d, c) :: ts => (n + 1 : ℤ) ^ d * c + totalExponent n ts

def factorCount (n : ℕ) : List Term → ℕ
  | [] => 0
  | (d, c) :: ts => c.natAbs * gap n d + factorCount n ts

/-- A definable finite witness for the entire product, with no word-problem oracle. -/
def familyWitness (n : ℕ) (H : ℤ) : (ts : List Term) →
    Witness (first n) (familyWord n H ts)
      (x ^ H * y ^ totalExponent n ts * x ^ (-H))
  | [] => Witness.ofEq (first n) (by simp [familyWord, totalExponent])
  | (d, c) :: ts =>
    ((blockWitness n H d c).mul (familyWitness n H ts)).change rfl (by
      simp only [totalExponent]
      group)

theorem familyWitness_length (n : ℕ) (H : ℤ) (ts : List Term) :
    (familyWitness n H ts).factors.length = factorCount n ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rcases t with ⟨d, c⟩
    simp only [familyWitness, Witness.factors_change, Witness.length_mul,
      blockWitness_length, ih, factorCount]

theorem familyWitness_sound (n : ℕ) (H : ℤ) (ts : List Term) :
    familyWord n H ts * product (first n) (familyWitness n H ts).factors =
      x ^ H * y ^ totalExponent n ts * x ^ (-H) :=
  (familyWitness n H ts).sound

/-- The required witness is constructed, so this family theorem has no witness premise. -/
theorem family_solvable (n : ℕ) (H : ℤ) (ts : List Term) :
    Reachable (pair (first n) (x⁻¹ * familyWord n H ts)) (standard 2) := by
  apply witnessed_power_conjugate_solvable n H (totalExponent n ts) (familyWord n H ts)
    (familyWitness n H ts).factors
  simpa only [mul_assoc] using congrArg (x⁻¹ * ·) (familyWitness_sound n H ts)

/-- The statement in the exact second-relator convention of the frozen metadata. -/
theorem family_metadata_solvable (n : ℕ) (H : ℤ) (ts : List Term) :
    Reachable (pair (first n) (x * (familyWord n H ts)⁻¹)) (standard 2) := by
  apply witnessed_power_conjugate_metadata_solvable n H (totalExponent n ts)
    (familyWord n H ts) (familyWitness n H ts).factors
  simpa only [mul_assoc] using congrArg (x⁻¹ * ·) (familyWitness_sound n H ts)

/-- A uniform bound for official primitives, including the metadata-convention bridge. -/
theorem family_metadata_counted (n : ℕ) (H : ℤ) (ts : List Term) :
    ∃ l ≤ 5 * factorCount n ts + (totalExponent n ts).natAbs + 22,
      Steps (pair (first n) (x * (familyWord n H ts)⁻¹)) l (standard 2) := by
  have hw : (x⁻¹ * familyWord n H ts) * product (first n) (familyWitness n H ts).factors =
      x⁻¹ * (x ^ H * y ^ totalExponent n ts * x ^ (-H)) := by
    simpa only [mul_assoc] using congrArg (x⁻¹ * ·) (familyWitness_sound n H ts)
  obtain ⟨l, hb, hl⟩ := witnessed_power_conjugate_metadata_counted n H
    (totalExponent n ts) (familyWord n H ts) (familyWitness n H ts).factors hw
  have hc := (cost_bounds (familyWitness n H ts).factors).2
  rw [familyWitness_length] at hc
  exact ⟨l, by omega, hl⟩

end AC.MillerSchupp.Divisibility
