import ACSquareResidueReduction

/-! The first nontrivial degree-three residual seed, replayed by the kernel. -/

namespace AC.MillerSchupp.SquareFamily.Residual
open AC.Certificate

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Frozen numbered certificate from `research/p3-family/seed-m1.json`. -/
def seedOneMoves : List ℕ := [0, 7, 11, 2, 10, 11, 5, 1, 10, 4, 11, 12, 3, 8, 8, 12, 5, 12, 10, 10, 10, 10, 13, 10, 6, 6, 6, 11, 5, 7, 7, 7, 10, 11, 11, 11, 4, 10, 10, 10, 12, 11, 11, 13, 11, 11, 11, 2, 10, 10, 10, 5, 12, 3, 3, 1, 7, 2, 2, 6, 2, 2, 5, 2, 8]

theorem seed_one_cost : primitiveCost seedOneMoves = 81 := by decide +kernel

theorem seed_one_encoded : EncodedSteps [[-2, -2, -2, 1, 1, 2, 2, 2, -1], [-2, -2, -1, 2, -1, -1]] 81 [[1], [2]] := by
  have h0 : EncodedSteps [[-2, -2, -2, 1, 1, 2, 2, 2, -1], [-2, -2, -1, 2, -1, -1]] 10 [[-2, -2, -2, -1, -1, 2, -1, 2, -1], [-2, -2, -2, -1, -1, 2, 2, 2, 1]] :=
    checkEncodedBetween_sound (ids := [0, 7, 11, 2, 10, 11, 5, 1]) (ms := [0, 7, 11, 2, 10, 11, 5, 1])
      (by decide +kernel) (by decide +kernel)
  have h1 : EncodedSteps [[-2, -2, -2, -1, -1, 2, -1, 2, -1], [-2, -2, -2, -1, -1, 2, 2, 2, 1]] 10 [[-2, -1, -1, 2, 1, 1, 1], [-2, -1, -1, -1, -1, 2, -1, -2]] :=
    checkEncodedBetween_sound (ids := [10, 4, 11, 12, 3, 8, 8, 12]) (ms := [10, 4, 11, 12, 3, 8, 8, 12])
      (by decide +kernel) (by decide +kernel)
  have h2 : EncodedSteps [[-2, -1, -1, 2, 1, 1, 1], [-2, -1, -1, -1, -1, 2, -1, -2]] 10 [[-2, -1, -1, 2, 1, 1, 1], [-2, -1, -1, -1, -2, -1, -1, 2, -1]] :=
    checkEncodedBetween_sound (ids := [5, 12, 10, 10, 10, 10, 13, 10]) (ms := [5, 12, 10, 10, 10, 10, 13, 10])
      (by decide +kernel) (by decide +kernel)
  have h3 : EncodedSteps [[-2, -1, -1, 2, 1, 1, 1], [-2, -1, -1, -1, -2, -1, -1, 2, -1]] 10 [[-2, -1, -1, 2, 1, 1, 1], [-1, -2, -1, -1, -1, -1, -1, -1]] :=
    checkEncodedBetween_sound (ids := [6, 6, 6, 11, 5, 7, 7, 7]) (ms := [6, 6, 6, 11, 5, 7, 7, 7])
      (by decide +kernel) (by decide +kernel)
  have h4 : EncodedSteps [[-2, -1, -1, 2, 1, 1, 1], [-1, -2, -1, -1, -1, -1, -1, -1]] 8 [[-2, -1, -1, 2, 1, 1, 1], [-2, -1, -1, -1, -1, -2, -1, -1, 2]] :=
    checkEncodedBetween_sound (ids := [10, 11, 11, 11, 4, 10, 10, 10]) (ms := [10, 11, 11, 11, 4, 10, 10, 10])
      (by decide +kernel) (by decide +kernel)
  have h5 : EncodedSteps [[-2, -1, -1, 2, 1, 1, 1], [-2, -1, -1, -1, -1, -2, -1, -1, 2]] 8 [[-2, -1, -1, -1, -1, -1], [-1, -1, -1, -2, -1, -1, -1]] :=
    checkEncodedBetween_sound (ids := [12, 11, 11, 13, 11, 11, 11, 2]) (ms := [12, 11, 11, 13, 11, 11, 11, 2])
      (by decide +kernel) (by decide +kernel)
  have h6 : EncodedSteps [[-2, -1, -1, -1, -1, -1], [-1, -1, -1, -2, -1, -1, -1]] 14 [[-2, -1, -1, -1], [1]] :=
    checkEncodedBetween_sound (ids := [10, 10, 10, 5, 12, 3, 3, 1]) (ms := [10, 10, 10, 5, 12, 3, 3, 1])
      (by decide +kernel) (by decide +kernel)
  have h7 : EncodedSteps [[-2, -1, -1, -1], [1]] 10 [[-2, 1, 2], [2]] :=
    checkEncodedBetween_sound (ids := [7, 2, 2, 6, 2, 2, 5, 2]) (ms := [7, 2, 2, 6, 2, 2, 5, 2])
      (by decide +kernel) (by decide +kernel)
  have h8 : EncodedSteps [[-2, 1, 2], [2]] 1 [[1], [2]] :=
    checkEncodedBetween_sound (ids := [8]) (ms := [8])
      (by decide +kernel) (by decide +kernel)
  exact ((((((((h0.trans h1).trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).trans h8)

theorem seed_one_steps : Steps (pair (P2.root 3) (relation 1 2)) 81 (standard 2) := by
  rcases seed_one_encoded with ⟨R, S, hr, hs, path⟩
  have ht : parseTuple [[1], [2]] = some target := by decide +kernel
  have he : S = target := Option.some.inj (hs.symm.trans ht)
  subst S
  have he : denote ((parseTuple [[-2, -2, -2, 1, 1, 2, 2, 2, -1], [-2, -2, -1, 2, -1, -1]]).getD target) =
      pair (P2.root 3) (relation 1 2) := by
    ext i
    fin_cases i <;> decide +kernel
  rw [hr, Option.getD_some] at he
  simpa only [he, denote_target] using path

theorem square_three_four :
    Reachable (Diagonal.generalSquare 3 4) (standard 2) :=
  (degree_three_iff 1).mpr seed_one_steps.reachable

end AC.MillerSchupp.SquareFamily.Residual
