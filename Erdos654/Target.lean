module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Geometry.Euclidean.Sphere.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic

@[expose] public section

namespace Erdos654

/-- The Euclidean plane, represented by complex coordinates with their usual metric. -/
abbrev Point := ℂ

open scoped Classical in
/-- The distinct distances from a point to all other points of a finite configuration. -/
noncomputable def pinnedDistances (points : Finset Point) (point : Point) : Finset ℝ :=
  (points.erase point).image (dist point)

open scoped Classical in
/-- Every circle contains at most three points of the configuration. -/
def NoFourConcyclic (points : Finset Point) : Prop :=
  ∀ center : Point, ∀ radius : ℝ,
    (points.filter fun point => dist point center = radius).card ≤ 3

/-- The optimal guaranteed largest pinned-distance count among configurations of the given size.
The maximum for the empty configuration is zero. The infimum is over natural-number counts. -/
noncomputable def optimalPinnedCount (size : ℕ) : ℕ :=
  sInf {count : ℕ | ∃ points : Finset Point, points.card = size ∧ NoFourConcyclic points ∧
    points.sup (fun point => (pinnedDistances points point).card) = count}

/-- No three distinct points of the configuration are collinear. -/
def NoThreeCollinear (points : Finset Point) : Prop :=
  ∀ triple : Finset Point, triple ⊆ points → triple.card = 3 →
    ¬ Collinear ℝ (triple : Set Point)

open scoped Classical in
/-- Every circle centered at a point of the configuration contains at most two other points. -/
def AtMostTwoPerCenteredCircle (points : Finset Point) : Prop :=
  ∀ center ∈ points, ∀ radius : ℝ,
    ((points.erase center).filter fun point => dist point center = radius).card ≤ 2

/-- The near-linear question in Erdős Problem 654, with an optional additional condition.
The error and size threshold are uniform over all configurations of the given size. -/
def NearLinearQuestion (condition : Finset Point → Prop) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ size : ℕ in Filter.atTop,
    ∀ points : Finset Point, points.card = size → NoFourConcyclic points → condition points →
      ∃ point ∈ points,
        (1 - epsilon) * size < (pinnedDistances points point).card

/-- The question whether a fixed positive improvement on the one-third bound holds eventually. -/
def ImprovedThirdQuestion (condition : Finset Point → Prop) : Prop :=
  ∃ improvement : ℝ, 0 < improvement ∧ ∀ᶠ size : ℕ in Filter.atTop,
    ∀ points : Finset Point, points.card = size → NoFourConcyclic points → condition points →
      ∃ point ∈ points,
        (1 / 3 + improvement) * size < (pinnedDistances points point).card

/-- The strong question without a restriction on collinear points. -/
def strongQuestion : Prop := NearLinearQuestion (fun _ => True)

/-- The weaker question without a restriction on collinear points. -/
def weakQuestion : Prop := ImprovedThirdQuestion (fun _ => True)

/-- The strong question with no three collinear points. -/
def generalPositionStrongQuestion : Prop := NearLinearQuestion NoThreeCollinear

/-- The one-third improvement question with no three collinear points. -/
def generalPositionWeakQuestion : Prop := ImprovedThirdQuestion NoThreeCollinear

/-- The near-linear suggestion under the extra centered-circle hypothesis on Bloom's page.
Its pairing with this bound is not confirmed in all original sources. -/
def centeredCircleSuggestion : Prop := NearLinearQuestion AtMostTwoPerCenteredCircle

/-- The explicit upper-bound family of Feng et al., arXiv:2601.22401v3, Section 3.1. -/
def CounterexampleFamily : Prop :=
  ∀ parameter : ℕ, 10 ≤ parameter → ∃ points : Finset Point,
    points.card = 4 * parameter ∧ NoFourConcyclic points ∧
      ∀ point ∈ points, (pinnedDistances points point).card ≤ 3 * parameter - 1

end Erdos654
