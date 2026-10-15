module

public import Count
public import RootObstruction

@[expose] public section

namespace ArborCounterexample
noncomputable section
open Polynomial

/-- The actual Ehrhart polynomial of `Forest.witness`, identified by all-m counts below. -/
def E : Polynomial ℝ := (X+1)^230*((7*X+2)^8*f*C (1/6144))

def IsEhrhart (t : Forest) (p : Polynomial ℝ) : Prop :=
  ∀ m : ℕ, p.eval (m:ℝ) = (Nat.card {x : t.Coord // t.Valid m x} : ℝ)

theorem E_counts_all_dilations : IsEhrhart Forest.witness E := by
  intro m
  have hq := Forest.witness_count m
  have hr := congrArg (fun q : ℚ => (q : ℝ)) hq.symm
  simpa [E,Forest.Eeval,Forest.fQ,f,div_eq_mul_inv] using hr

theorem E_has_nonreal_root : ∃ z : ℂ,
    (E.map (algebraMap ℝ ℂ)).eval z=0 ∧ z.im≠0 := by
  obtain ⟨z,hz,hi⟩ := f_has_nonreal_root
  refine ⟨z, ?_, hi⟩
  simp only [E, Polynomial.map_mul, Polynomial.eval_mul, hz, mul_zero, zero_mul]

theorem ehrhart_unique (t : Forest) (p q : Polynomial ℝ)
    (hp : IsEhrhart t p) (hq : IsEhrhart t q) : p=q := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective (Nat.cast_injective (R := ℝ))).mono
  rintro x ⟨n,rfl⟩
  exact (hp n).trans (hq n).symm

/-- A genuine singleton-block arbor, its all-m Ehrhart polynomial, and a
nonreal complex root. No polynomial-only certificate is assumed in the bridge. -/
theorem complete_counterexample :
    ∃ (t : Forest) (p : Polynomial ℝ) (z : ℂ),
      (∃ children, t=Forest.root children) ∧ t.size=243 ∧
      IsEhrhart t p ∧ (p.map (algebraMap ℝ ℂ)).eval z=0 ∧ z.im≠0 := by
  obtain ⟨z,hz,hi⟩ := E_has_nonreal_root
  exact ⟨Forest.witness,E,z,⟨_,rfl⟩,Forest.witness_size,E_counts_all_dilations,hz,hi⟩

#print axioms E_counts_all_dilations
#print axioms ehrhart_unique
#print axioms complete_counterexample

end
end ArborCounterexample
