module

public import Erdos654.Target
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The elementary one-third bound for Erdős Problem 654

Partition the other points according to their distance from a fixed point.
The hypothesis that no four points lie on a circle bounds each part by three.
This proves only the elementary baseline, not an improvement on one third.
-/

@[expose] public section

namespace Erdos654

/-- Every point determines at least one third as many distances as there are other points. -/
theorem third_lower_bound (points : Finset Point) (point : Point)
    (noFour : NoFourConcyclic points) (point_mem : point ∈ points) :
    points.card - 1 ≤ 3 * (pinnedDistances points point).card := by
  classical
  calc
    points.card - 1 = (points.erase point).card :=
      (Finset.card_erase_of_mem point_mem).symm
    _ = ∑ radius ∈ pinnedDistances points point,
        ((points.erase point).filter fun other => dist point other = radius).card :=
      Finset.card_eq_sum_card_image (dist point) (points.erase point)
    _ ≤ ∑ _radius ∈ pinnedDistances points point, 3 := by
      apply Finset.sum_le_sum
      intro radius _radius_mem
      calc
        ((points.erase point).filter fun other => dist point other = radius).card ≤
            (points.filter fun other => dist other point = radius).card := by
          apply Finset.card_le_card
          intro other other_mem
          obtain ⟨other_mem, distance_eq⟩ := Finset.mem_filter.mp other_mem
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_of_mem_erase other_mem, (dist_comm other point).trans distance_eq⟩
        _ ≤ 3 := noFour point radius
    _ = 3 * (pinnedDistances points point).card := by simp [Nat.mul_comm]

end Erdos654
