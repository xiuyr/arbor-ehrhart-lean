module

public import Main

@[expose] public section

namespace ArborCounterexample
open Polynomial

/-- Zero dilation contains exactly one lattice point; the polynomial is nonzero. -/
theorem E_at_zero : E.eval (0 : ℝ) = 1 := by
  norm_num [E, f]

theorem E_ne_zero : E ≠ 0 := by
  intro h
  have hz := E_at_zero
  rw [h] at hz
  norm_num at hz

/-- The real-root assertion already fails on the allowed singleton-block arbors. -/
theorem not_all_arbor_ehrhart_roots_real :
    ¬ (∀ (t : Forest) (p : Polynomial ℝ),
      (∃ children, t = Forest.root children) → IsEhrhart t p →
      ∀ z : ℂ, (p.map (algebraMap ℝ ℂ)).eval z = 0 → z.im = 0) := by
  intro h
  obtain ⟨t, p, z, ht, _hs, hp, hz, hi⟩ := complete_counterexample
  exact hi (h t p ht hp z hz)

#check IsEhrhart
#check complete_counterexample
#print axioms E_at_zero
#print axioms E_ne_zero
#print axioms E_counts_all_dilations
#print axioms complete_counterexample
#print axioms not_all_arbor_ehrhart_roots_real
end ArborCounterexample
