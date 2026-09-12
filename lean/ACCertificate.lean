import ACDeferral
import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Sound ordinary discovery certificates

The executable checker below uses the fourteen frozen `ac-r2-v1` move IDs.
Its soundness theorem is against the unchanged official `AC.Step` relation.
One numbered inverse-right multiplication expands to three official steps.
-/

namespace AC.Certificate

variable {n : ℕ}

/-- A finite path with its number of official primitive steps exposed. -/
inductive Steps {n : ℕ} : Relators n → ℕ → Relators n → Prop
  | refl (R : Relators n) : Steps R 0 R
  | tail {R S : Relators n} {k : ℕ} (h : Steps R k S) {T : Relators n}
      (step : Step S T) : Steps R (k + 1) T

theorem Steps.reachable {R S : Relators n} {k : ℕ} (h : Steps R k S) :
    Reachable R S := by
  induction h with
  | refl => exact .refl _
  | tail _ step ih => exact ih.trans (.single step)

theorem Steps.single {R S : Relators n} (h : Step R S) : Steps R 1 S :=
  (Steps.refl R).tail h

theorem Steps.trans {R S T : Relators n} {k l : ℕ}
    (h : Steps R k S) (h' : Steps S l T) : Steps R (k + l) T := by
  induction h' with
  | refl => simpa using h
  | tail _ step ih => exact ih.tail step

/-- The source relator is inverted and restored, so no inverse multiplication is assumed. -/
theorem Steps.mulInvRight (R : Relators n) (i j : Fin n) (hij : i ≠ j) :
    Steps R 3 (Function.update R i (R i * (R j)⁻¹)) := by
  let R₁ := Function.update R j (R j)⁻¹
  let R₂ := Function.update R₁ i (R₁ i * R₁ j)
  let R₃ := Function.update R₂ j (R₂ j)⁻¹
  have heq : R₃ = Function.update R i (R i * (R j)⁻¹) := by
    ext k
    by_cases hki : k = i
    · subst k; simp [R₃, R₂, R₁, hij, hij.symm]
    · by_cases hkj : k = j
      · subst k; simp [R₃, R₂, R₁, hij, hij.symm]
      · simp [R₃, R₂, R₁, hki, hkj]
  rw [← heq]
  exact ((Steps.single (Step.inv R j)).tail (Step.mulRight R₁ i j hij)).tail
    (Step.inv R₂ j)

/-- A signed generator: `true` is positive. -/
abbrev Letter (n : ℕ) := Fin n × Bool
abbrev RawWord (n : ℕ) := List (Letter n)
abbrev RawTuple (n : ℕ) := Fin n → RawWord n

def denote (R : RawTuple n) : Relators n := fun i => FreeGroup.mk (R i)

theorem denote_update (R : RawTuple n) (i : Fin n) (w : RawWord n) :
    denote (Function.update R i w) = Function.update (denote R) i (FreeGroup.mk w) := by
  ext j
  by_cases h : j = i
  · subst j; simp [denote]
  · simp [denote, h]

/-- Typed ordinary moves. Distinctness is required by construction. -/
inductive Move (n : ℕ)
  | inv (i : Fin n)
  | mulRight (i j : Fin n) (distinct : i ≠ j)
  | mulInvRight (i j : Fin n) (distinct : i ≠ j)
  | conj (i : Fin n) (c : Letter n)

def Move.cost : Move n → ℕ
  | .mulInvRight .. => 3
  | _ => 1

/-- Normalize after every operation; intermediate words stay explicit and finite. -/
def Move.apply (R : RawTuple n) : Move n → RawTuple n
  | .inv i => Function.update R i (FreeGroup.invRev (R i))
  | .mulRight i j _ => Function.update R i (FreeGroup.reduce (R i ++ R j))
  | .mulInvRight i j _ =>
      Function.update R i (FreeGroup.reduce (R i ++ FreeGroup.invRev (R j)))
  | .conj i c => Function.update R i
      (FreeGroup.reduce ([c] ++ R i ++ FreeGroup.invRev [c]))

/-- Every typed move expands into exactly the stated number of official steps. -/
theorem Move.sound (R : RawTuple n) (m : Move n) :
    Steps (denote R) m.cost (denote (m.apply R)) := by
  cases m with
  | inv i =>
    simpa [Move.apply, Move.cost, denote_update, ← FreeGroup.inv_mk, denote] using
      Steps.single (Step.inv (denote R) i)
  | mulRight i j h =>
    simpa [Move.apply, Move.cost, denote_update, FreeGroup.reduce.self,
      ← FreeGroup.mul_mk, denote] using Steps.single (Step.mulRight (denote R) i j h)
  | mulInvRight i j h =>
    simpa [Move.apply, Move.cost, denote_update, FreeGroup.reduce.self,
      ← FreeGroup.mul_mk, ← FreeGroup.inv_mk, denote] using
      Steps.mulInvRight (denote R) i j h
  | conj i c =>
    simpa only [Move.apply, Move.cost, denote_update, FreeGroup.reduce.self,
      ← FreeGroup.mul_mk, ← FreeGroup.inv_mk, denote] using
      Steps.single (Step.conj (denote R) i (FreeGroup.mk [c]))

/-- Exact frozen `ac-r2-v1` ID translation. Every other natural number is rejected. -/
def decode : ℕ → Option (Move 2)
  | 0 => some (.inv 0)
  | 1 => some (.inv 1)
  | 2 => some (.mulRight 0 1 (by decide))
  | 3 => some (.mulInvRight 0 1 (by decide))
  | 4 => some (.mulRight 1 0 (by decide))
  | 5 => some (.mulInvRight 1 0 (by decide))
  | 6 => some (.conj 0 (0, true))
  | 7 => some (.conj 0 (0, false))
  | 8 => some (.conj 0 (1, true))
  | 9 => some (.conj 0 (1, false))
  | 10 => some (.conj 1 (0, true))
  | 11 => some (.conj 1 (0, false))
  | 12 => some (.conj 1 (1, true))
  | 13 => some (.conj 1 (1, false))
  | _ => none

/-- Total accounting function; successful replay separately establishes ID validity. -/
def primitiveCost (ids : List ℕ) : ℕ :=
  (ids.map fun id => if id = 3 ∨ id = 5 then 3 else 1).sum

theorem decode_cost {id : ℕ} {m : Move 2} (h : decode id = some m) :
    m.cost = if id = 3 ∨ id = 5 then 3 else 1 := by
  unfold decode at h
  split at h <;> cases h <;> rfl

theorem primitiveCost_bounds (ids : List ℕ) :
    ids.length ≤ primitiveCost ids ∧ primitiveCost ids ≤ 3 * ids.length := by
  induction ids with
  | nil => simp [primitiveCost]
  | cons id ids ih =>
    change ids.length + 1 ≤ (if id = 3 ∨ id = 5 then 3 else 1) + primitiveCost ids ∧
      (if id = 3 ∨ id = 5 then 3 else 1) + primitiveCost ids ≤ 3 * (ids.length + 1)
    split <;> omega

def replay (R : RawTuple 2) : List ℕ → Option (RawTuple 2)
  | [] => some R
  | id :: ids => do
      let m ← decode id
      replay (m.apply R) ids

/-- Accepted replay gives a counted official path; no assumption about the solver is used. -/
theorem replay_sound {R S : RawTuple 2} {ids : List ℕ}
    (h : replay R ids = some S) : Steps (denote R) (primitiveCost ids) (denote S) := by
  induction ids generalizing R with
  | nil =>
    simp [replay] at h
    subst S
    exact Steps.refl _
  | cons id ids ih =>
    cases hd : decode id with
    | none => simp [replay, hd] at h
    | some m =>
      have ht : replay (m.apply R) ids = some S := by simpa [replay, hd] using h
      simpa [primitiveCost, decode_cost hd] using (m.sound R).trans (ih ht)

def target : RawTuple 2 := fun i => [(i, true)]

@[simp] theorem denote_target : denote target = standard 2 := rfl

/-- Exact ordered endpoint, without free relator permutations or ignored inversions. -/
def check (R : RawTuple 2) (ids : List ℕ) : Bool :=
  match replay R ids with
  | none => false
  | some S => decide (S = target)

theorem check_counted_sound {R : RawTuple 2} {ids : List ℕ} (h : check R ids = true) :
    Steps (denote R) (primitiveCost ids) (standard 2) := by
  unfold check at h
  cases hr : replay R ids with
  | none => simp [hr] at h
  | some S =>
    have hs : S = target := by simpa [hr] using h
    subst S
    simpa using replay_sound hr

theorem check_sound {R : RawTuple 2} {ids : List ℕ} (h : check R ids = true) :
    Reachable (denote R) (standard 2) := (check_counted_sound h).reachable

/-- Recorded intermediate states are untrusted witnesses, checked at every step. -/
abbrev Trace := List (ℕ × RawTuple 2)

def traceCost (trace : Trace) : ℕ := primitiveCost (trace.map Prod.fst)

/-- Checking explicit intermediate states avoids growing replay expressions in proof terms. -/
def checkTrace (R : RawTuple 2) : Trace → Bool
  | [] => decide (R = target)
  | (id, S) :: rest =>
      match decode id with
      | none => false
      | some m => decide (m.apply R = S) && checkTrace S rest

/-- Extra intermediate-state witnesses do not change the numbered replay semantics. -/
theorem checkTrace_replay {R : RawTuple 2} {trace : Trace}
    (h : checkTrace R trace = true) : replay R (trace.map Prod.fst) = some target := by
  induction trace generalizing R with
  | nil =>
    have hr : R = target := by simpa [checkTrace] using h
    simp [replay, hr]
  | cons entry rest ih =>
    rcases entry with ⟨id, S⟩
    cases hd : decode id with
    | none => simp [checkTrace, hd] at h
    | some m =>
      have hs : m.apply R = S ∧ checkTrace S rest = true := by
        simpa [checkTrace, hd] using h
      simpa [replay, hd, hs.1] using ih hs.2

theorem checkTrace_counted_sound {R : RawTuple 2} {trace : Trace}
    (h : checkTrace R trace = true) : Steps (denote R) (traceCost trace) (standard 2) := by
  induction trace generalizing R with
  | nil =>
    have hr : R = target := by simpa [checkTrace] using h
    subst R
    exact Steps.refl _
  | cons entry rest ih =>
    rcases entry with ⟨id, S⟩
    cases hd : decode id with
    | none => simp [checkTrace, hd] at h
    | some m =>
      have hs : m.apply R = S ∧ checkTrace S rest = true := by
        simpa [checkTrace, hd] using h
      have first := m.sound R
      rw [hs.1] at first
      simpa [traceCost, primitiveCost, decode_cost hd] using first.trans (ih hs.2)

theorem checkTrace_sound {R : RawTuple 2} {trace : Trace}
    (h : checkTrace R trace = true) : Reachable (denote R) (standard 2) :=
  (checkTrace_counted_sound h).reachable

/-- The signed integer alphabet is exactly `1, -1, 2, -2`. -/
def parseLetter : ℤ → Option (Letter 2)
  | 1 => some (0, true)
  | -1 => some (0, false)
  | 2 => some (1, true)
  | -2 => some (1, false)
  | _ => none

def parseWord (w : List ℤ) : Option (RawWord 2) := w.mapM parseLetter

/-- Exactly two relators, in their supplied order. Empty words are allowed. -/
def parseTuple : List (List ℤ) → Option (RawTuple 2)
  | [a, b] => do
      let a' ← parseWord a
      let b' ← parseWord b
      pure (fun i => if i = 0 then a' else b')
  | _ => none

def parseId : ℤ → Option ℕ
  | .ofNat id => some id
  | .negSucc _ => none

def parseIds (ids : List ℤ) : Option (List ℕ) := ids.mapM parseId

def checkEncoded (words : List (List ℤ)) (ids : List ℤ) : Bool :=
  match parseTuple words, parseIds ids with
  | some R, some ms => check R ms
  | _, _ => false

/-- The parsed input tuple has an ordinary path to the exact standard tuple. -/
def EncodedSolvable (words : List (List ℤ)) : Prop :=
  ∃ R, parseTuple words = some R ∧ Reachable (denote R) (standard 2)

theorem checkEncoded_sound {words : List (List ℤ)} {ids : List ℤ}
    (h : checkEncoded words ids = true) : EncodedSolvable words := by
  cases hr : parseTuple words with
  | none => simp [checkEncoded, hr] at h
  | some R =>
    cases hm : parseIds ids with
    | none => simp [checkEncoded, hm] at h
    | some ms =>
      exact ⟨R, hr, check_sound (by simpa [checkEncoded, hr, hm] using h)⟩

abbrev EncodedTrace := List (ℤ × List (List ℤ))

def parseTrace (trace : EncodedTrace) : Option Trace := trace.mapM fun (id, words) => do
  let m ← parseId id
  let R ← parseTuple words
  pure (m, R)

def checkEncodedTrace (words : List (List ℤ)) (trace : EncodedTrace) : Bool :=
  match parseTuple words, parseTrace trace with
  | some R, some ts => checkTrace R ts
  | _, _ => false

theorem checkEncodedTrace_sound {words : List (List ℤ)} {trace : EncodedTrace}
    (h : checkEncodedTrace words trace = true) : EncodedSolvable words := by
  cases hr : parseTuple words with
  | none => simp [checkEncodedTrace, hr] at h
  | some R =>
    cases ht : parseTrace trace with
    | none => simp [checkEncodedTrace, ht] at h
    | some ts =>
      exact ⟨R, hr, checkTrace_sound (by simpa [checkEncodedTrace, hr, ht] using h)⟩

/-- Parsed endpoints with an explicit official primitive-step count. -/
def EncodedSteps (start : List (List ℤ)) (k : ℕ) (finish : List (List ℤ)) : Prop :=
  ∃ R S, parseTuple start = some R ∧ parseTuple finish = some S ∧ Steps (denote R) k (denote S)

def checkBetween (R S : RawTuple 2) (ids : List ℕ) : Bool :=
  match replay R ids with
  | none => false
  | some T => decide (T = S)

theorem checkBetween_sound {R S : RawTuple 2} {ids : List ℕ}
    (h : checkBetween R S ids = true) : Steps (denote R) (primitiveCost ids) (denote S) := by
  unfold checkBetween at h
  cases ht : replay R ids with
  | none => simp [ht] at h
  | some T =>
    have hs : T = S := by simpa [ht] using h
    subst T
    exact replay_sound ht

def checkEncodedBetween (start finish : List (List ℤ)) (ids : List ℤ) : Bool :=
  match parseTuple start, parseTuple finish, parseIds ids with
  | some R, some S, some ms => checkBetween R S ms
  | _, _, _ => false

/-- Segments are checked independently, then composed by their exact parsed endpoints. -/
theorem checkEncodedBetween_sound {start finish : List (List ℤ)} {ids : List ℤ}
    {ms : List ℕ} (hm : parseIds ids = some ms)
    (h : checkEncodedBetween start finish ids = true) :
    EncodedSteps start (primitiveCost ms) finish := by
  cases hr : parseTuple start with
  | none => simp [checkEncodedBetween, hr] at h
  | some R =>
    cases hs : parseTuple finish with
    | none => simp [checkEncodedBetween, hr, hs] at h
    | some S =>
      exact ⟨R, S, hr, hs, checkBetween_sound (by
        simpa [checkEncodedBetween, hr, hs, hm] using h)⟩

theorem EncodedSteps.trans {a b c : List (List ℤ)} {k l : ℕ}
    (h : EncodedSteps a k b) (h' : EncodedSteps b l c) : EncodedSteps a (k + l) c := by
  rcases h with ⟨R, S, hr, hs, path⟩
  rcases h' with ⟨S', T, hs', ht, path'⟩
  have heq : S = S' := Option.some.inj (hs.symm.trans hs')
  subst S'
  exact ⟨R, T, hr, ht, path.trans path'⟩

theorem EncodedSteps.solvable {words : List (List ℤ)} {k : ℕ}
    (h : EncodedSteps words k [[1], [2]]) : EncodedSolvable words := by
  rcases h with ⟨R, S, hr, hs, path⟩
  have ht : parseTuple [[1], [2]] = some target := by decide
  have heq : S = target := Option.some.inj (hs.symm.trans ht)
  subst S
  exact ⟨R, hr, by simpa using path.reachable⟩

/-- An accepted ordinary certificate also gives a no-additions stable certificate to empty. -/
theorem check_noAdd {R : RawTuple 2} {ids : List ℕ} (h : check R ids = true) :
    NoAddReachable ⟨2, denote R⟩ ⟨0, standard 0⟩ :=
  (noAdd_to_empty_iff_ordinary (denote R)).mpr (check_sound h)

end AC.Certificate
