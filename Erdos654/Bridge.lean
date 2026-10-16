module

public import Erdos654.Target
public import Erdos654.TwoAxis

@[expose] public section

namespace Erdos654

/-- The reproduced two-axis construction satisfies the full quantified counterexample family. -/
theorem counterexampleFamily : CounterexampleFamily := by
  intro parameter hparameter
  obtain ⟨points, hcard, hcircle, hbound⟩ := JSP000530.counterexample_family parameter
  refine ⟨points, hcard, hcircle, ?_⟩
  intro point hpoint
  have hcount := hbound point hpoint
  change (pinnedDistances points point).card < 3 * parameter at hcount
  omega

/-- The near-linear part of Erdős Problem 654 is false without the no-three-collinear condition. -/
theorem not_strongQuestion : ¬ strongQuestion := by
  intro hypothesis
  apply JSP000530.not_asymptotically_all_distances
  intro epsilon hepsilon
  obtain ⟨cutoff, hcutoff⟩ := Filter.eventually_atTop.mp (hypothesis epsilon hepsilon)
  refine ⟨cutoff, ?_⟩
  intro points hsize hcircle
  obtain ⟨point, hpoint, hbound⟩ :=
    hcutoff points.card hsize points rfl hcircle trivial
  exact ⟨point, hpoint, le_of_lt hbound⟩

end Erdos654
