import ACSquareHeightFiveSeed
import ACSquareP3Families

/-! The residual seed completes every integer degree at square height five. -/
namespace AC.MillerSchupp.SquareFamily.HeightFive

theorem square_three_five :
    Reachable (Diagonal.generalSquare 3 5) (standard 2) :=
  P2.divisibility_square_solvable 3 5 (by decide)

theorem square_five_all (p : ℤ) :
    Reachable (pair (square 5 6) (SquareFamily.relation p 5)) (standard 2) := by
  have hlo := Int.emod_nonneg p (by decide : (11 : ℤ) ≠ 0)
  have hhi := Int.emod_lt_of_pos p (by decide : (0 : ℤ) < 11)
  have he := Int.emod_add_mul_ediv p 11
  by_cases h3 : p % 11 = 3
  · have hp : p = 3 + (5 + 6) * (p / 11) := by omega
    rw [hp]
    exact (square_period 3 5 6 (p / 11)).mp square_three_five
  by_cases h8 : p % 11 = 8
  · have hp : p = -3 + (5 + 6) * (p / 11 + 1) := by omega
    rw [hp]
    exact (square_period (-3) 5 6 (p / 11 + 1)).mp
      (negative_solvable 3 5 6 square_three_five)
  by_cases h4 : p % 11 = 4
  · have hp : p = 4 + (5 + 6) * (p / 11) := by omega
    rw [hp]
    exact (square_period 4 5 6 (p / 11)).mp square_four_five
  by_cases h7 : p % 11 = 7
  · have hp : p = -4 + (5 + 6) * (p / 11 + 1) := by omega
    rw [hp]
    exact (square_period (-4) 5 6 (p / 11 + 1)).mp
      (negative_solvable 4 5 6 square_four_five)
  apply P2.covered_positive 5 p
  change ∃ r t : ℤ, p = r + 11 * t ∧
    (r = 0 ∨ r = 1 ∨ r = -1 ∨ r = 5 ∨ r = -5 ∨ r = 2 ∨ r = -2)
  by_cases h : p % 11 ≤ 5
  · exact ⟨p % 11, p / 11, by omega, by omega⟩
  · exact ⟨p % 11 - 11, p / 11 + 1, by omega, by omega⟩

theorem complementary_six_all (p : ℤ) :
    Reachable (pair (square 6 5) (SquareFamily.relation p 6)) (standard 2) := by
  have he : square 6 5 = square 5 6 := by norm_num [square]
  have ht := (complement_steps p 6 5).reachable
  rw [he] at ht ⊢
  exact ht.trans (square_five_all p)

theorem exponent_ten_slice (b c : ℤ) :
    Reachable (presentation 10 5 b c) (standard 2) :=
  even_of_square 5 b c (square_five_all b)

theorem exponent_eleven_slice (a c : ℤ) :
    Reachable (presentation 11 a 6 c) (standard 2) :=
  odd_of_square 5 a c (complementary_six_all a)

end AC.MillerSchupp.SquareFamily.HeightFive
