import ACSubstitution
import Mathlib.Tactic.Group

/-!
# Constructive algebra of normal-closure witnesses

All operations retain explicit ordered lists of conjugates of a fixed relator.
No quotient equality or choice operation is used to extract a witness.
-/

namespace AC.Substitution

variable {n : ℕ}

def conjugateFactors (g : Word n) (fs : List (Factor n)) : List (Factor n) :=
  fs.map fun f => (g * f.1, f.2)

def inverseFactors (fs : List (Factor n)) : List (Factor n) :=
  fs.reverse.map fun f => (f.1, !f.2)

@[simp] theorem product_append (r : Word n) (fs gs : List (Factor n)) :
    product r (fs ++ gs) = product r fs * product r gs := by
  induction fs with
  | nil => simp [product]
  | cons f fs ih => simp [product, ih, mul_assoc]

@[simp] theorem product_conjugateFactors (r g : Word n) (fs : List (Factor n)) :
    product r (conjugateFactors g fs) = g * product r fs * g⁻¹ := by
  induction fs with
  | nil => simp [conjugateFactors, product]
  | cons f fs ih =>
    simp only [conjugateFactors, List.map_cons, product] at *
    rw [ih]
    simp only [Factor.value]
    group

theorem factor_inverse (r : Word n) (f : Factor n) :
    Factor.value r (f.1, !f.2) = (f.value r)⁻¹ := by
  rcases f with ⟨g, b⟩
  cases b <;> simp [Factor.value, mul_assoc]

@[simp] theorem product_inverseFactors (r : Word n) (fs : List (Factor n)) :
    product r (inverseFactors fs) = (product r fs)⁻¹ := by
  induction fs with
  | nil => simp [inverseFactors, product]
  | cons f fs ih =>
    simp only [inverseFactors, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, product_append, product, mul_one] at *
    rw [ih, factor_inverse]
    simp

@[simp] theorem length_conjugateFactors (g : Word n) (fs : List (Factor n)) :
    (conjugateFactors g fs).length = fs.length := by simp [conjugateFactors]

@[simp] theorem length_inverseFactors (fs : List (Factor n)) :
    (inverseFactors fs).length = fs.length := by simp [inverseFactors]

@[simp] theorem cost_append (fs gs : List (Factor n)) :
    cost (fs ++ gs) = cost fs + cost gs := by
  induction fs with
  | nil => simp [cost]
  | cons f fs ih => simp [cost, ih, Nat.add_assoc]

@[simp] theorem cost_conjugateFactors (g : Word n) (fs : List (Factor n)) :
    cost (conjugateFactors g fs) = cost fs := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp only [conjugateFactors, List.map_cons, cost] at *
    rw [ih]
    rfl

theorem cost_inverseFactors (fs : List (Factor n)) :
    cost (inverseFactors fs) + cost fs = 8 * fs.length := by
  induction fs with
  | nil => simp [inverseFactors, cost]
  | cons f fs ih =>
    simp only [inverseFactors, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, cost_append, cost, List.length_cons] at *
    rcases f with ⟨g, b⟩
    cases b <;> simp only [Factor.cost, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte] at * <;> omega

/-- A finite, ordered right-multiplication witness from `u` to `v`. -/
structure Witness (r u v : Word n) where
  factors : List (Factor n)
  sound : u * product r factors = v

namespace Witness

variable {r u v w a b u' v' : Word n}

def refl (r u : Word n) : Witness r u u :=
  ⟨[], by simp [product]⟩

def ofEq (r : Word n) (h : u = v) : Witness r u v :=
  ⟨[], by simpa [product] using h⟩

def change (h : Witness r u v) (hu : u = u') (hv : v = v') : Witness r u' v' :=
  ⟨h.factors, by simpa only [← hu, ← hv] using h.sound⟩

@[simp] theorem factors_change (h : Witness r u v) (hu : u = u') (hv : v = v') :
    (h.change hu hv).factors = h.factors := rfl

def source (r : Word n) : Witness r r 1 :=
  ⟨[(1, false)], by simp [product, Factor.value]⟩

def trans (h : Witness r u v) (h' : Witness r v w) : Witness r u w :=
  ⟨h.factors ++ h'.factors, by rw [product_append, ← mul_assoc, h.sound, h'.sound]⟩

def mul (h : Witness r u v) (h' : Witness r a b) : Witness r (u * a) (v * b) :=
  ⟨conjugateFactors a⁻¹ h.factors ++ h'.factors, by
    rw [product_append, product_conjugateFactors]
    calc
      u * a * (a⁻¹ * product r h.factors * (a⁻¹)⁻¹ * product r h'.factors) =
          (u * product r h.factors) * (a * product r h'.factors) := by group
      _ = v * b := by rw [h.sound, h'.sound]⟩

def conj (h : Witness r u v) (g : Word n) :
    Witness r (g * u * g⁻¹) (g * v * g⁻¹) :=
  ⟨conjugateFactors g h.factors, by
    rw [product_conjugateFactors]
    calc
      g * u * g⁻¹ * (g * product r h.factors * g⁻¹) =
          g * (u * product r h.factors) * g⁻¹ := by group
      _ = g * v * g⁻¹ := by rw [h.sound]⟩

def reverse (h : Witness r u v) : Witness r v u :=
  ⟨inverseFactors h.factors, by
    rw [product_inverseFactors]
    calc
      v * (product r h.factors)⁻¹ =
          (u * product r h.factors) * (product r h.factors)⁻¹ :=
        congrArg (· * (product r h.factors)⁻¹) h.sound.symm
      _ = u := by group⟩

def inverse (h : Witness r u v) : Witness r u⁻¹ v⁻¹ :=
  ⟨conjugateFactors u (inverseFactors h.factors), by
    rw [product_conjugateFactors, product_inverseFactors]
    calc
      u⁻¹ * (u * (product r h.factors)⁻¹ * u⁻¹) =
          (u * product r h.factors)⁻¹ := by group
      _ = v⁻¹ := congrArg Inv.inv h.sound⟩

def pow (h : Witness r u v) : (m : ℕ) → Witness r (u ^ m) (v ^ m)
  | 0 => ofEq r (by simp)
  | m + 1 => ((pow h m).mul h).change (pow_succ u m).symm (pow_succ v m).symm

def zpow (h : Witness r u v) : (m : ℤ) → Witness r (u ^ m) (v ^ m)
  | .ofNat m => (h.pow m).change (by simp) (by simp)
  | .negSucc m => ((h.pow (m + 1)).inverse).change (by simp [zpow_negSucc])
      (by simp [zpow_negSucc])

@[simp] theorem length_refl (r u : Word n) : (refl r u).factors.length = 0 := rfl

@[simp] theorem length_trans (h : Witness r u v) (h' : Witness r v w) :
    (h.trans h').factors.length = h.factors.length + h'.factors.length := by
  simp [trans]

@[simp] theorem length_mul (h : Witness r u v) (h' : Witness r a b) :
    (h.mul h').factors.length = h.factors.length + h'.factors.length := by
  simp [mul]

@[simp] theorem length_conj (h : Witness r u v) (g : Word n) :
    (h.conj g).factors.length = h.factors.length := by simp [conj]

@[simp] theorem length_reverse (h : Witness r u v) :
    h.reverse.factors.length = h.factors.length := by simp [reverse]

@[simp] theorem length_inverse (h : Witness r u v) :
    h.inverse.factors.length = h.factors.length := by simp [inverse]

@[simp] theorem length_pow (h : Witness r u v) (m : ℕ) :
    (h.pow m).factors.length = m * h.factors.length := by
  induction m with
  | zero => simp [pow, ofEq]
  | succ m ih => simp [pow, ih, Nat.add_mul]

@[simp] theorem length_zpow (h : Witness r u v) (m : ℤ) :
    (h.zpow m).factors.length = m.natAbs * h.factors.length := by
  cases m <;> simp [zpow]

@[simp] theorem cost_trans (h : Witness r u v) (h' : Witness r v w) :
    cost (h.trans h').factors = cost h.factors + cost h'.factors := by simp [trans]

@[simp] theorem cost_mul (h : Witness r u v) (h' : Witness r a b) :
    cost (h.mul h').factors = cost h.factors + cost h'.factors := by simp [mul]

@[simp] theorem cost_conj (h : Witness r u v) (g : Word n) :
    cost (h.conj g).factors = cost h.factors := by simp [conj]

@[simp] theorem cost_pow (h : Witness r u v) (m : ℕ) :
    cost (h.pow m).factors = m * cost h.factors := by
  induction m with
  | zero => simp [pow, ofEq, cost]
  | succ m ih => simp [pow, ih, Nat.add_mul]

theorem cost_inverse (h : Witness r u v) :
    cost h.inverse.factors + cost h.factors = 8 * h.factors.length := by
  simpa [inverse] using cost_inverseFactors h.factors

end Witness

end AC.Substitution
