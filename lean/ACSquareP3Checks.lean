import ACSquareP3Families

/-! Boundary cases and logical dependency reports for the degree-three continuation. -/

namespace AC.MillerSchupp.SquareFamily.ResidualChecks

example (p r : ℤ) (m : ℕ) :
    Reachable (Diagonal.generalSquare p (p * m + r)) (standard 2) ↔
    Reachable (pair (P2.root p) (Residual.relation r ((2 : ℤ) ^ m))) (standard 2) :=
  Residual.square_residual_iff p r m

example : Reachable (Diagonal.generalSquare 3 4) (standard 2) :=
  Residual.square_three_four
example : Reachable (Diagonal.generalSquare (-3) 4) (standard 2) :=
  Residual.square_four_all (-3)
example : Reachable (Diagonal.generalSquare 111 4) (standard 2) :=
  Residual.square_four_all 111
example : Reachable (pair (square 5 4) (relation (-111) 5)) (standard 2) :=
  Residual.complementary_five_all (-111)
example : Reachable (presentation 8 4 (-111) 29) (standard 2) :=
  Residual.exponent_eight_slice (-111) 29
example : Reachable (presentation 9 111 5 (-29)) (standard 2) :=
  Residual.exponent_nine_slice 111 (-29)

end AC.MillerSchupp.SquareFamily.ResidualChecks

#print axioms AC.MillerSchupp.SquareFamily.Residual.relation
#print axioms AC.MillerSchupp.SquareFamily.Residual.reductionWitness
#print axioms AC.MillerSchupp.SquareFamily.Residual.root_to_residual
#print axioms AC.MillerSchupp.SquareFamily.Residual.inverseEntryMap
#print axioms AC.MillerSchupp.SquareFamily.Residual.inverseEntryMap_x
#print axioms AC.MillerSchupp.SquareFamily.Residual.inverseEntryMap_y
#print axioms AC.MillerSchupp.SquareFamily.Residual.inverseEntryMap_standard
#print axioms AC.MillerSchupp.SquareFamily.Residual.inverseEntryMap_pair
#print axioms AC.MillerSchupp.SquareFamily.Residual.square_root_iff
#print axioms AC.MillerSchupp.SquareFamily.Residual.square_residual_iff
#print axioms AC.MillerSchupp.SquareFamily.Residual.degree_three_iff
#print axioms AC.MillerSchupp.SquareFamily.Residual.degree_three_base
#print axioms AC.MillerSchupp.SquareFamily.Residual.seedOneMoves
#print axioms AC.MillerSchupp.SquareFamily.Residual.seed_one_cost
#print axioms AC.MillerSchupp.SquareFamily.Residual.seed_one_encoded
#print axioms AC.MillerSchupp.SquareFamily.Residual.seed_one_steps
#print axioms AC.MillerSchupp.SquareFamily.Residual.square_three_four
#print axioms AC.MillerSchupp.SquareFamily.Residual.square_four_all
#print axioms AC.MillerSchupp.SquareFamily.Residual.complementary_five_all
#print axioms AC.MillerSchupp.SquareFamily.Residual.exponent_eight_slice
#print axioms AC.MillerSchupp.SquareFamily.Residual.exponent_nine_slice
