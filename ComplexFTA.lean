module

/-
The short proof below is adapted verbatim from mathlib's
Mathlib/Analysis/Complex/Polynomial/Basic.lean at revision
a3a10db0e9d66acbebf76c5e6a135066525ac900, Apache-2.0,
authors Chris Hughes, Junyan Xu, Yury Kudryashov.
This local version avoids that file's unrelated polynomial Galois-group
and finite-dimensional-extension imports to stay within the 2 GiB cap.
It proves the theorem; it does not introduce an axiom or certificate oracle.
-/
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

open Polynomial Bornology Complex

namespace ArborCounterexample

theorem complex_exists_root {f : ℂ[X]} (hf : 0 < degree f) : ∃ z : ℂ, IsRoot f z := by
  by_contra! hf'
  have (z : ℂ) : (f.eval z)⁻¹ = 0 :=
    (f.differentiable.inv hf').apply_eq_of_tendsto_cocompact z <|
      Metric.cobounded_eq_cocompact (α := ℂ) ▸ (Filter.tendsto_inv₀_cobounded.comp <| by
        simpa only [tendsto_norm_atTop_iff_cobounded]
          using f.tendsto_norm_atTop hf tendsto_norm_cobounded_atTop)
  obtain rfl : f = C 0 := Polynomial.funext fun z ↦ inv_injective <| by simp [this]
  simp at hf

noncomputable instance complexIsAlgClosed : IsAlgClosed ℂ :=
  IsAlgClosed.of_exists_root _ fun _p _ hp => complex_exists_root <| degree_pos_of_irreducible hp

#print axioms complexIsAlgClosed

end ArborCounterexample
