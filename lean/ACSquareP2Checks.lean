import ACSquareP2Families

/-! Boundary cases for both parities, sign/period transport, and the full N=7 slice. -/

namespace AC.MillerSchupp.SquareFamily.P2Checks

example (s : ℕ) : Reachable (Diagonal.generalSquare 2 s) (standard 2) :=
  P2.square_p2_solvable s
example : Reachable (Diagonal.generalSquare 2 0) (standard 2) := P2.square_p2_solvable 0
example : Reachable (Diagonal.generalSquare 2 3) (standard 2) := P2.square_p2_solvable 3
example : Reachable (Diagonal.generalSquare 2 4) (standard 2) := P2.square_p2_solvable 4
example : Reachable (pair (square 5 6) (relation 24 5)) (standard 2) := by
  apply P2.covered_positive 5 24
  exact ⟨2, 2, by norm_num, by simp⟩
example : Reachable (pair (square 6 5) (relation (-24) 6)) (standard 2) := by
  apply P2.covered_negative 5 (-24)
  exact ⟨-2, -2, by norm_num, by simp⟩
example : Reachable (presentation 6 3 (-107) 19) (standard 2) :=
  P2.exponent_six_slice (-107) 19
example : Reachable (presentation 7 107 4 (-19)) (standard 2) :=
  P2.exponent_seven_slice 107 (-19)
example : Reachable (presentation 20 10 (-2) 99) (standard 2) :=
  P2.even_negative_p2_family 10 99
example : Reachable (presentation 21 2 11 (-99)) (standard 2) :=
  P2.odd_p2_family 10 (-99)

example (p s : ℤ) : AC.Certificate.Steps (Diagonal.normalForm p s) 43
    (AC.WordTransport.applyHom (P2.entryMap p s) (pair (P2.root p) (P2.companion s))) :=
  P2.root_entry p s
example : Reachable (Diagonal.generalSquare 0 0) (standard 2) :=
  P2.divisibility_square_solvable 0 0 (Or.inl (dvd_refl 0))
example : Reachable (Diagonal.generalSquare 3 5) (standard 2) :=
  P2.divisibility_square_solvable 3 5 (by norm_num)
example : Reachable (Diagonal.generalSquare 3 6) (standard 2) :=
  P2.divisibility_square_solvable 3 6 (by norm_num)
example : Reachable (presentation 46 23 6 (-7)) (standard 2) :=
  P2.even_divisibility_family 23 6 (-7) (by norm_num)

end AC.MillerSchupp.SquareFamily.P2Checks

#print axioms AC.MillerSchupp.SquareFamily.P2.root
#print axioms AC.MillerSchupp.SquareFamily.P2.companion
#print axioms AC.MillerSchupp.SquareFamily.P2.powerRelator
#print axioms AC.MillerSchupp.SquareFamily.P2.doubleWitness
#print axioms AC.MillerSchupp.SquareFamily.P2.iteratedDouble
#print axioms AC.MillerSchupp.SquareFamily.P2.power_finish
#print axioms AC.MillerSchupp.SquareFamily.P2.multiple_root_solvable
#print axioms AC.MillerSchupp.SquareFamily.P2.predecessor_multiple_root_solvable
#print axioms AC.MillerSchupp.SquareFamily.P2.even_root_solvable
#print axioms AC.MillerSchupp.SquareFamily.P2.odd_root_solvable
#print axioms AC.MillerSchupp.SquareFamily.P2.root_solvable
#print axioms AC.MillerSchupp.SquareFamily.P2.entryMap
#print axioms AC.MillerSchupp.SquareFamily.P2.entryMap_x
#print axioms AC.MillerSchupp.SquareFamily.P2.entryMap_y
#print axioms AC.MillerSchupp.SquareFamily.P2.root_entry
#print axioms AC.MillerSchupp.SquareFamily.P2.entryMap_standard
#print axioms AC.MillerSchupp.SquareFamily.P2.square_of_root
#print axioms AC.MillerSchupp.SquareFamily.P2.square_p2_solvable
#print axioms AC.MillerSchupp.SquareFamily.P2.covered_positive
#print axioms AC.MillerSchupp.SquareFamily.P2.covered_negative
#print axioms AC.MillerSchupp.SquareFamily.P2.even_p2_family
#print axioms AC.MillerSchupp.SquareFamily.P2.even_negative_p2_family
#print axioms AC.MillerSchupp.SquareFamily.P2.odd_p2_family
#print axioms AC.MillerSchupp.SquareFamily.P2.odd_negative_p2_family
#print axioms AC.MillerSchupp.SquareFamily.P2.square_three_all
#print axioms AC.MillerSchupp.SquareFamily.P2.complementary_four_all
#print axioms AC.MillerSchupp.SquareFamily.P2.exponent_six_slice
#print axioms AC.MillerSchupp.SquareFamily.P2.exponent_seven_slice
#print axioms AC.MillerSchupp.SquareFamily.P2.multiple_square_solvable
#print axioms AC.MillerSchupp.SquareFamily.P2.predecessor_multiple_square_solvable
#print axioms AC.MillerSchupp.SquareFamily.P2.divisibility_square_solvable
#print axioms AC.MillerSchupp.SquareFamily.P2.even_divisibility_family
#print axioms AC.MillerSchupp.SquareFamily.P2.odd_divisibility_family
