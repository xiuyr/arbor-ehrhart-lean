module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Arbor Ehrhart nonreal-root counterexample: independent statement

An allowed singleton-labeled arbor is a rooted tree. Forest.root introduces
one vertex; Forest.pair is disjoint union and adds no vertex. Coord assigns
one nonnegative integer to each vertex. Valid requires, at every vertex,
that the sum on its subtree is at most m times that subtree's size. Thus
Nat.card counts precisely the lattice points in the m-th dilation of the
arbor polytope, including m=0. The witness has a chain of two top vertices
above one 180-leaf star and ten 5-leaf stars (243 vertices in total).

The five compared declarations assert the all-dilation formula, a nonreal
complex root, a complete existential counterexample, uniqueness of the
counting polynomial, and the negation of universal real-rootedness. No
claim about the separate h*-root assertion or smallest witness is made.

This Challenge is an isolated specification, not a proof: its deliberate
sorry placeholders are required only for statement comparison. Solution
imports the fully proved development instead, never this file. Proof code
must pass its transitive axiom audit without sorryAx or native computation.
-/

@[expose] public section
namespace ArborCounterexample
noncomputable section
open Polynomial

/-- An ordered forest of rooted trees with singleton label blocks.
`root f` adds one labelled vertex whose descendants are all vertices of `f`.
`pair` takes disjoint union and adds no vertex; `empty` has no vertices. -/
inductive Forest where
  | empty : Forest
  | pair : Forest → Forest → Forest
  | root : Forest → Forest

namespace Forest

/-- The number of singleton-labeled vertices; disjoint union adds sizes. -/
def size : Forest → ℕ
  | empty => 0
  | pair f g => size f+size g
  | root f => 1+size f

/-- One nonnegative integer coordinate for each singleton vertex. -/
def Coord : Forest → Type
  | empty => Unit
  | pair f g => Coord f × Coord g
  | root f => ℕ × Coord f

/-- Sum of all coordinates in the given forest or rooted subtree. -/
def height : (f : Forest) → Coord f → ℕ
  | empty, _ => 0
  | pair f g, x => height f x.1+height g x.2
  | root f, x => x.1+height f x.2

/-- Exactly the subtree inequalities of the arbor at integer dilation `m`.
Each `root` imposes its descendant-sum constraint, and recursion imposes
the corresponding constraint at every descendant vertex. -/
def Valid (m : ℕ) : (f : Forest) → Coord f → Prop
  | empty, _ => True
  | pair f g, x => Valid m f x.1 ∧ Valid m g x.2
  | root f, x => Valid m f x.2 ∧ height (root f) x ≤ m*size (root f)

/-- Disjoint union of the specified number of copies, with distinct vertex positions. -/
def copies (f : Forest) : ℕ → Forest
  | 0 => empty
  | k+1 => pair f (copies f k)
/-- The rooted tree consisting of a single vertex. -/
abbrev leaf : Forest := root empty
/-- A new root above k disjoint one-vertex children. -/
def star (k : ℕ) : Forest := root (copies leaf k)
/-- Two top vertices above one 180-leaf star and ten 5-leaf stars. -/
def witness : Forest := root (root (pair (star 180) (copies (star 5) 10)))


end Forest

/-- The explicit real quintic responsible for the nonreal root. -/
noncomputable def f : Polynomial ℝ :=
  C 24 + C 5852 * X + C 400056 * X^2 + C 8533751 * X^3 +
    C 44368122 * X^4 + C 67184474 * X^5

/-- The actual Ehrhart polynomial of `Forest.witness`, identified by all-m counts below. -/
def E : Polynomial ℝ := (X+1)^230*((7*X+2)^8*f*C (1/6144))

/-- Equality with the actual nonnegative integral coordinate count at every natural dilation. -/
def IsEhrhart (t : Forest) (p : Polynomial ℝ) : Prop :=
  ∀ m : ℕ, p.eval (m:ℝ) = (Nat.card {x : t.Coord // t.Valid m x} : ℝ)


/-- The explicit polynomial counts actual lattice points for every dilation. -/
theorem E_counts_all_dilations : IsEhrhart Forest.witness E := by sorry

/-- The explicit Ehrhart polynomial has a complex root outside the real line. -/
theorem E_has_nonreal_root : ∃ z : ℂ,
    (E.map (algebraMap ℝ ℂ)).eval z = 0 ∧ z.im ≠ 0 := by sorry

/-- A rooted singleton arbor of size 243 contradicts universal real-rootedness. -/
theorem complete_counterexample :
    ∃ (t : Forest) (p : Polynomial ℝ) (z : ℂ),
      (∃ children, t = Forest.root children) ∧ t.size = 243 ∧
      IsEhrhart t p ∧ (p.map (algebraMap ℝ ℂ)).eval z = 0 ∧ z.im ≠ 0 := by sorry

/-- Agreement with the lattice count at every natural dilation fixes the polynomial. -/
theorem ehrhart_unique (t : Forest) (p q : Polynomial ℝ)
    (hp : IsEhrhart t p) (hq : IsEhrhart t q) : p = q := by sorry

/-- The universal real-root assertion fails already for singleton-labeled arbors. -/
theorem not_all_arbor_ehrhart_roots_real :
    ¬ (∀ (t : Forest) (p : Polynomial ℝ),
      (∃ children, t = Forest.root children) → IsEhrhart t p →
      ∀ z : ℂ, (p.map (algebraMap ℝ ℂ)).eval z = 0 → z.im = 0) := by sorry

end
end ArborCounterexample
