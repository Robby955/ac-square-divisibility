import ACSquareP2Entry

/-! Sign, period and original-coordinate consequences of the uniform p=2 proof. -/

namespace AC.MillerSchupp.SquareFamily.P2

/-- Seven covered residue representatives, including both new interior slices. -/
theorem covered_positive (m : ℕ) (p : ℤ)
    (hp : ∃ r t : ℤ, p = r + (2 * m + 1) * t ∧
      (r = 0 ∨ r = 1 ∨ r = -1 ∨ r = m ∨ r = -(m : ℤ) ∨ r = 2 ∨ r = -2)) :
    Reachable (pair (square m (m + 1)) (relation p m)) (standard 2) := by
  obtain ⟨r, t, hp, hr⟩ := hp
  have he : p = r + ((m : ℤ) + (m + 1)) * t := by rw [hp]; ring
  rw [he]
  apply (square_period r m (m + 1) t).mp
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact zero_square_solvable m
  · exact even_square_solvable m
  · exact negative_solvable 1 m (m + 1) (even_square_solvable m)
  · exact Diagonal.solvable m
  · exact negative_solvable m m (m + 1) (Diagonal.solvable m)
  · exact square_p2_solvable m
  · exact negative_solvable 2 m (m + 1) (square_p2_solvable m)

theorem covered_negative (m : ℕ) (p : ℤ)
    (hp : ∃ r t : ℤ, p = r + (2 * m + 1) * t ∧
      (r = 0 ∨ r = 1 ∨ r = -1 ∨ r = m ∨ r = -(m : ℤ) ∨ r = 2 ∨ r = -2)) :
    Reachable (pair (square (m + 1) m) (relation p (m + 1))) (standard 2) := by
  have he : square (m + 1) m = square m (m + 1) := by
    unfold square
    congr 2
    omega
  have ht := (complement_steps p (m + 1) m).reachable
  rw [he] at ht ⊢
  exact ht.trans (covered_positive m p hp)

theorem even_p2_family (m : ℕ) (c : ℤ) :
    Reachable (presentation (2 * m) m 2 c) (standard 2) :=
  even_of_square m 2 c (square_p2_solvable m)

theorem even_negative_p2_family (m : ℕ) (c : ℤ) :
    Reachable (presentation (2 * m) m (-2) c) (standard 2) :=
  even_of_square m (-2) c (negative_solvable 2 m (m + 1) (square_p2_solvable m))

theorem odd_p2_family (m : ℕ) (c : ℤ) :
    Reachable (presentation (2 * m + 1) 2 (m + 1) c) (standard 2) := by
  apply odd_of_square m 2 c
  apply covered_negative m 2
  exact ⟨2, 0, by ring, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))⟩

theorem odd_negative_p2_family (m : ℕ) (c : ℤ) :
    Reachable (presentation (2 * m + 1) (-2) (m + 1) c) (standard 2) := by
  apply odd_of_square m (-2) c
  apply covered_negative m (-2)
  exact ⟨-2, 0, by ring, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))⟩

private theorem residues_seven (p : ℤ) : ∃ r t : ℤ, p = r + 7 * t ∧
    (r = 0 ∨ r = 1 ∨ r = -1 ∨ r = 3 ∨ r = -3 ∨ r = 2 ∨ r = -2) := by
  have hlo := Int.emod_nonneg p (by decide : (7 : ℤ) ≠ 0)
  have hhi := Int.emod_lt_of_pos p (by decide : (0 : ℤ) < 7)
  have he := Int.emod_add_mul_ediv p 7
  by_cases h : p % 7 ≤ 3
  · exact ⟨p % 7, p / 7, by omega, by omega⟩
  · exact ⟨p % 7 - 7, p / 7 + 1, by omega, by omega⟩

/-- All square-family residues with square exponent seven are now covered. -/
theorem square_three_all (p : ℤ) :
    Reachable (pair (square 3 4) (relation p 3)) (standard 2) := by
  apply covered_positive 3 p
  simpa using residues_seven p

theorem complementary_four_all (p : ℤ) :
    Reachable (pair (square 4 3) (relation p 4)) (standard 2) := by
  apply covered_negative 3 p
  simpa using residues_seven p

theorem exponent_six_slice (b c : ℤ) :
    Reachable (presentation 6 3 b c) (standard 2) := even_of_square 3 b c (square_three_all b)

theorem exponent_seven_slice (a c : ℤ) :
    Reachable (presentation 7 a 4 c) (standard 2) := odd_of_square 3 a c (complementary_four_all a)

/-- A whole two-parameter divisibility subfamily follows from the root entry. -/
theorem multiple_square_solvable (p : ℤ) (m : ℕ) :
    Reachable (Diagonal.generalSquare p (p * m)) (standard 2) :=
  square_of_root p (p * m) (multiple_root_solvable p m)

theorem predecessor_multiple_square_solvable (p : ℤ) (m : ℕ) :
    Reachable (Diagonal.generalSquare p (p * m + (p - 1))) (standard 2) :=
  square_of_root p (p * m + (p - 1)) (predecessor_multiple_root_solvable p m)

/-- Divisibility is an entry condition with supplied witnesses, not a quotient oracle. -/
theorem divisibility_square_solvable (p s : ℕ)
    (hd : p ∣ s ∨ p ∣ s + 1) :
    Reachable (Diagonal.generalSquare p s) (standard 2) := by
  rcases hd with ⟨m, hm⟩ | ⟨k, hk⟩
  · have he : (s : ℤ) = (p : ℤ) * (m : ℤ) := by exact_mod_cast hm
    rw [he]
    exact multiple_square_solvable p m
  · have hkpos : 0 < k := by nlinarith
    have hcast : (s : ℤ) + 1 = (p : ℤ) * (k : ℤ) := by exact_mod_cast hk
    have he : (s : ℤ) = (p : ℤ) * ((k - 1 : ℕ) : ℤ) + ((p : ℤ) - 1) := by
      have hk' : (k : ℤ) = ((k - 1 : ℕ) : ℤ) + 1 := by omega
      rw [hk'] at hcast
      nlinarith
    rw [he]
    exact predecessor_multiple_square_solvable p (k - 1)

theorem even_divisibility_family (m p : ℕ) (c : ℤ)
    (hd : p ∣ m ∨ p ∣ m + 1) :
    Reachable (presentation (2 * m) m p c) (standard 2) :=
  even_of_square m p c (divisibility_square_solvable p m hd)

theorem odd_divisibility_family (m p : ℕ) (c : ℤ)
    (hd : p ∣ m ∨ p ∣ m + 1) :
    Reachable (presentation (2 * m + 1) p (m + 1) c) (standard 2) := by
  apply odd_of_square m p c
  have he : square (m + 1) m = square m (m + 1) := by
    unfold square
    congr 2
    omega
  have ht := (complement_steps p (m + 1) m).reachable
  rw [he] at ht ⊢
  exact ht.trans (divisibility_square_solvable p m hd)

end AC.MillerSchupp.SquareFamily.P2
