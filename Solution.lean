module

public import Erdos654

@[expose] public section

namespace Palomar654

open scoped Classical in
/-- Distinct Euclidean distances to the other points, excluding the chosen point. -/
noncomputable def distanceValues (points : Finset ℂ) (point : ℂ) : Finset ℝ :=
  (points.erase point).image (dist point)

open scoped Classical in
/-- Every Euclidean circle contains at most three selected points. -/
def NoFourConcyclic (points : Finset ℂ) : Prop :=
  ∀ center : ℂ, ∀ radius : ℝ,
    (points.filter fun point => dist point center = radius).card ≤ 3

/-- For every parameter, there is a configuration of four times that many points with no four
concyclic and fewer than three times that many distinct distances from every point.
This is the two-axis counterexample to the near-linear part of Erdős Problem 654. -/
theorem counterexample_family (parameter : ℕ) :
    ∃ points : Finset ℂ, points.card = 4 * parameter ∧ NoFourConcyclic points ∧
      ∀ point ∈ points, (distanceValues points point).card < 3 * parameter := by
  exact JSP000530.counterexample_family parameter

/-- No-four-concyclic alone does not force a point with asymptotically all distances distinct.
This refutes only the near-linear part, not the weaker one-third improvement question. -/
theorem not_near_linear :
    ¬ (∀ epsilon : ℝ, 0 < epsilon → ∃ cutoff : ℕ, ∀ points : Finset ℂ,
      cutoff ≤ points.card → NoFourConcyclic points →
        ∃ point ∈ points,
          (1 - epsilon) * (points.card : ℝ) ≤ (distanceValues points point).card) := by
  exact JSP000530.not_asymptotically_all_distances

/-- The elementary one-third lower bound holds at each selected point. -/
theorem third_lower_bound (points : Finset ℂ) (point : ℂ)
    (noFour : NoFourConcyclic points) (point_mem : point ∈ points) :
    points.card - 1 ≤ 3 * (distanceValues points point).card := by
  exact Erdos654.third_lower_bound points point noFour point_mem

end Palomar654
