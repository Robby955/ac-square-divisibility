import ACSquareDiagonalFamilies

/-! A two-factor replacement for the original four-factor period schedule.
The original module and its source hash remain unchanged. -/
namespace AC.MillerSchupp.SquareFamily
open AC.Certificate AC.Substitution AC.WordTransport

def squarePeriodTwoWitness (p s k : ℤ) :
    Witness (square s k)
      (y ^ (s + k) * relation p s * (y ^ (s + k))⁻¹)
      (relation (p + (s + k)) s) := by
  let W := y ^ p * x * y ^ (-s) * x⁻¹ * y ^ (-p - (s + k))
  refine ⟨[(W⁻¹ * x⁻¹ * y ^ (-(s + k)), true),
           (W⁻¹ * y ^ (-(s + k)), false)], ?_⟩
  dsimp [W, product, Factor.value, square, relation]
  group

theorem squarePeriodTwoWitness_length (p s k : ℤ) :
    (squarePeriodTwoWitness p s k).factors.length = 2 := rfl

theorem squarePeriodTwoWitness_cost (p s k : ℤ) :
    cost (squarePeriodTwoWitness p s k).factors = 8 := rfl

theorem square_period_two_steps (p s k : ℤ) :
    Steps (pair (square s k) (relation p s)) 9
      (pair (square s k) (relation (p + (s + k)) s)) := by
  let w := squarePeriodTwoWitness p s k
  have h₁ := Steps.single (Step.conj
    (pair (square s k) (relation p s)) 1 (y ^ (s + k)))
  simp only [pair_one, pair_update_one] at h₁
  have h₂ := replace
    (pair (square s k) (y ^ (s + k) * relation p s * (y ^ (s + k))⁻¹))
    1 0 (by decide) w.factors _ w.sound
  simp only [pair_update_one, w, squarePeriodTwoWitness_cost] at h₂
  exact h₁.trans h₂

end AC.MillerSchupp.SquareFamily
