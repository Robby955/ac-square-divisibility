import ACSquareP3Seed

/-! The residual seed completes all square-family residues at exponent nine. -/

namespace AC.MillerSchupp.SquareFamily.Residual

/-- A finite residual certificate and the existing period theorem cover every integer residue. -/
theorem square_four_all (p : ℤ) :
    Reachable (pair (square 4 5) (SquareFamily.relation p 4)) (standard 2) := by
  have hlo := Int.emod_nonneg p (by decide : (9 : ℤ) ≠ 0)
  have hhi := Int.emod_lt_of_pos p (by decide : (0 : ℤ) < 9)
  have he := Int.emod_add_mul_ediv p 9
  by_cases h3 : p % 9 = 3
  · have hp : p = 3 + (4 + 5) * (p / 9) := by omega
    rw [hp]
    exact (square_period 3 4 5 (p / 9)).mp square_three_four
  by_cases h6 : p % 9 = 6
  · have hp : p = -3 + (4 + 5) * (p / 9 + 1) := by omega
    rw [hp]
    exact (square_period (-3) 4 5 (p / 9 + 1)).mp
      (negative_solvable 3 4 5 square_three_four)
  apply P2.covered_positive 4 p
  change ∃ r t : ℤ, p = r + 9 * t ∧
    (r = 0 ∨ r = 1 ∨ r = -1 ∨ r = 4 ∨ r = -4 ∨ r = 2 ∨ r = -2)
  by_cases h : p % 9 ≤ 4
  · exact ⟨p % 9, p / 9, by omega, by omega⟩
  · exact ⟨p % 9 - 9, p / 9 + 1, by omega, by omega⟩

theorem complementary_five_all (p : ℤ) :
    Reachable (pair (square 5 4) (SquareFamily.relation p 5)) (standard 2) := by
  have he : square 5 4 = square 4 5 := by norm_num [square]
  have ht := (complement_steps p 5 4).reachable
  rw [he] at ht ⊢
  exact ht.trans (square_four_all p)

theorem exponent_eight_slice (b c : ℤ) :
    Reachable (presentation 8 4 b c) (standard 2) :=
  even_of_square 4 b c (square_four_all b)

theorem exponent_nine_slice (a c : ℤ) :
    Reachable (presentation 9 a 5 c) (standard 2) :=
  odd_of_square 4 a c (complementary_five_all a)

end AC.MillerSchupp.SquareFamily.Residual
