module

public import Moments
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace ArborCounterexample
noncomputable section

/-- An ordered forest of rooted trees with singleton label blocks.
`root f` adds one labelled vertex whose descendants are all vertices of `f`.
`pair` takes disjoint union and adds no vertex; `empty` has no vertices. -/
inductive Forest where
  | empty : Forest
  | pair : Forest → Forest → Forest
  | root : Forest → Forest

namespace Forest

def size : Forest → ℕ
  | empty => 0
  | pair f g => size f+size g
  | root f => 1+size f

/-- One nonnegative integer coordinate for each singleton vertex. -/
def Coord : Forest → Type
  | empty => Unit
  | pair f g => Coord f × Coord g
  | root f => ℕ × Coord f

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

structure Population where
  Carrier : Type
  fintype : Fintype Carrier
  deficit : Carrier → ℕ

@[reducible] def population (m : ℕ) : Forest → Population
  | empty => ⟨Unit, inferInstance, fun _ => 0⟩
  | pair f g =>
    let p := population m f
    let q := population m g
    letI := p.fintype
    letI := q.fintype
    ⟨p.Carrier × q.Carrier, inferInstance, fun x => p.deficit x.1+q.deficit x.2⟩
  | root f =>
    let p := population m f
    letI := p.fintype
    ⟨Lift m p.deficit, inferInstance, liftDef⟩

abbrev Config (m : ℕ) (f : Forest) := (population m f).Carrier
instance configFintype (m : ℕ) (f : Forest) : Fintype (Config m f) :=
  (population m f).fintype
abbrev deficit (m : ℕ) (f : Forest) := (population m f).deficit

def encode (m : ℕ) : (f : Forest) → Config m f → Coord f
  | empty, _ => ()
  | pair f g, x => (encode m f x.1, encode m g x.2)
  | root f, x => (m+deficit m f x.1-x.2.val, encode m f x.1)

theorem encode_ok (m : ℕ) (f : Forest) (x : Config m f) :
    Valid m f (encode m f x) ∧
    height f (encode m f x)+deficit m f x=m*size f := by
  induction f with
  | empty => simp [Valid, encode, height, deficit, population, size]
  | pair f g ihf ihg =>
    rcases ihf x.1 with ⟨hvf,hef⟩
    rcases ihg x.2 with ⟨hvg,heg⟩
    change (Valid m f (encode m f x.1) ∧ Valid m g (encode m g x.2)) ∧ _
    refine ⟨⟨hvf,hvg⟩, ?_⟩
    change height f (encode m f x.1)+height g (encode m g x.2)+
      (deficit m f x.1+deficit m g x.2)=m*(size f+size g)
    rw [Nat.mul_add]
    omega
  | root f ih =>
    rcases ih x.1 with ⟨hv,he⟩
    have hx := x.2.isLt
    change x.2.val < m+deficit m f x.1+1 at hx
    have hd : x.2.val ≤ m+deficit m f x.1 := by omega
    have hh : height (root f) (encode m (root f) x)+x.2.val=m*(1+size f) := by
      change (m+deficit m f x.1-x.2.val)+height f (encode m f x.1)+x.2.val=_
      rw [Nat.mul_add, Nat.mul_one]
      omega
    refine ⟨⟨hv, ?_⟩, hh⟩
    change height (root f) (encode m (root f) x) ≤ m*(1+size f)
    omega

theorem encode_injective (m : ℕ) (f : Forest) : Function.Injective (encode m f) := by
  induction f with
  | empty => intro a b _; cases a; cases b; rfl
  | pair f g ihf ihg =>
    intro a b h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    apply Prod.ext
    · exact ihf h1
    · exact ihg h2
  | root f ih =>
    rintro ⟨a,i⟩ ⟨b,j⟩ h
    have hc : a=b := ih (congrArg Prod.snd h)
    subst b
    have hr := congrArg Prod.fst h
    have hi := i.isLt
    have hj := j.isLt
    change i.val < m+deficit m f a+1 at hi
    change j.val < m+deficit m f a+1 at hj
    have hij : i.val=j.val := by
      change m+deficit m f a-i.val=m+deficit m f a-j.val at hr
      omega
    have := Fin.ext hij
    subst j
    rfl

theorem encode_surjective (m : ℕ) (f : Forest) (y : Coord f) (hy : Valid m f y) :
    ∃ x : Config m f, encode m f x=y := by
  induction f with
  | empty => cases y; exact ⟨(), rfl⟩
  | pair f g ihf ihg =>
    obtain ⟨a,ha⟩ := ihf y.1 hy.1
    obtain ⟨b,hb⟩ := ihg y.2 hy.2
    exact ⟨(a,b), Prod.ext ha hb⟩
  | root f ih =>
    obtain ⟨a,ha⟩ := ih y.2 hy.1
    have he := (encode_ok m f a).2
    rw [ha] at he
    have hyb := hy.2
    change y.1+height f y.2 ≤ m*(1+size f) at hyb
    rw [Nat.mul_add, Nat.mul_one] at hyb
    have hb : y.1 ≤ m+deficit m f a := by omega
    let i : Fin (m+deficit m f a+1) := ⟨m+deficit m f a-y.1, by omega⟩
    refine ⟨⟨a,i⟩, ?_⟩
    apply Prod.ext
    · change m+deficit m f a-(m+deficit m f a-y.1)=y.1
      omega
    · exact ha

def latticeEquiv (m : ℕ) (f : Forest) : Config m f ≃ {x : Coord f // Valid m f x} :=
  Equiv.ofBijective (fun x => ⟨encode m f x,(encode_ok m f x).1⟩)
    ⟨fun a b h => encode_injective m f (congrArg Subtype.val h),
      fun ⟨y,hy⟩ => by
        obtain ⟨x,hx⟩ := encode_surjective m f y hy
        exact ⟨x,Subtype.ext hx⟩⟩

def moments (m : ℕ) (f : Forest) (r : ℕ) : ℚ := moment (deficit m f) r

theorem lattice_count_eq_moment (m : ℕ) (f : Forest) :
    (Nat.card {x : Coord f // Valid m f x} : ℚ)=moments m f 0 := by
  rw [← Nat.card_congr (latticeEquiv m f)]
  simp [moments, moment, Nat.card_eq_fintype_card]

#print axioms lattice_count_eq_moment

end Forest
end
end ArborCounterexample
