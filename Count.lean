module

public import Arbor

@[expose] public section

namespace ArborCounterexample
noncomputable section
namespace Forest

def copies (f : Forest) : ℕ → Forest
  | 0 => empty
  | k+1 => pair f (copies f k)
abbrev leaf : Forest := root empty
def star (k : ℕ) : Forest := root (copies leaf k)
def witness : Forest := root (root (pair (star 180) (copies (star 5) 10)))

theorem size_copies (f : Forest) (k : ℕ) : size (copies f k)=k*size f := by
  induction k with
  | zero => simp [copies,size]
  | succ k ih => simp [copies,size,ih,Nat.add_mul,Nat.add_comm]

theorem witness_size : size witness=243 := by
  norm_num [witness,star,leaf,size,size_copies]

theorem moments_empty0 (m : ℕ) : moments m empty 0=1 := by
  simp [moments,moment,configFintype,deficit,population]
theorem moments_empty_pos (m r : ℕ) : moments m empty (r+1)=0 := by
  simp [moments,moment,configFintype,deficit,population]

theorem pair_moments0 (m : ℕ) (f g : Forest) :
    moments m (pair f g) 0=moments m f 0*moments m g 0 :=
  prod_moment0 (deficit m f) (deficit m g)
theorem pair_moments1 (m : ℕ) (f g : Forest) :
    moments m (pair f g) 1=moments m f 1*moments m g 0+
      moments m f 0*moments m g 1 := prod_moment1 _ _
theorem pair_moments2 (m : ℕ) (f g : Forest) :
    moments m (pair f g) 2=moments m f 2*moments m g 0+
      2*moments m f 1*moments m g 1+moments m f 0*moments m g 2 :=
  prod_moment2 _ _
theorem pair_moments3 (m : ℕ) (f g : Forest) :
    moments m (pair f g) 3=moments m f 3*moments m g 0+
      3*moments m f 2*moments m g 1+3*moments m f 1*moments m g 2+
      moments m f 0*moments m g 3 := prod_moment3 _ _

theorem root_moments0 (m : ℕ) (f : Forest) :
    moments m (root f) 0=(m+1)*moments m f 0+moments m f 1 := lift_moment0 _ _
theorem root_moments1 (m : ℕ) (f : Forest) :
    moments m (root f) 1=(m*(m+1)*moments m f 0+
      (2*m+1)*moments m f 1+moments m f 2)/2 := lift_moment1 _ _
theorem root_moments2 (m : ℕ) (f : Forest) :
    moments m (root f) 2=((2*m^3+3*m^2+m)*moments m f 0+
      (6*m^2+6*m+1)*moments m f 1+(6*m+3)*moments m f 2+
      2*moments m f 3)/6 := lift_moment2 _ _

theorem copies_moments (m k : ℕ) (f : Forest) (c u v w : ℚ)
    (h0 : moments m f 0=c) (h1 : moments m f 1=c*u)
    (h2 : moments m f 2=c*v) (h3 : moments m f 3=c*w) :
    moments m (copies f k) 0=c^k ∧
    moments m (copies f k) 1=c^k*(k*u) ∧
    moments m (copies f k) 2=c^k*(k*v+k*(k-1)*u^2) ∧
    moments m (copies f k) 3=c^k*(k*w+3*k*(k-1)*u*v+k*(k-1)*(k-2)*u^3) := by
  induction k with
  | zero => simp [copies,moments_empty0,moments_empty_pos]
  | succ k ih =>
    rcases ih with ⟨i0,i1,i2,i3⟩
    simp only [copies,pair_moments0,pair_moments1,pair_moments2,pair_moments3,
      h0,h1,h2,h3,i0,i1,i2,i3,Nat.cast_add,Nat.cast_one,pow_succ]
    constructor
    · ring
    constructor
    · ring
    constructor <;> ring

def mu1 (m : ℚ) := m/2
def mu2 (m : ℚ) := m*(2*m+1)/6
def mu3 (m : ℚ) := m^2*(m+1)/4
def s1 (k : ℕ) (m : ℚ) := k*mu1 m
def s2 (k : ℕ) (m : ℚ) := k*mu2 m+k*(k-1)*(mu1 m)^2
def s3 (k : ℕ) (m : ℚ) := k*mu3 m+3*k*(k-1)*mu1 m*mu2 m+
  k*(k-1)*(k-2)*(mu1 m)^3

theorem leaf_moments (m : ℕ) :
    moments m leaf 0=m+1 ∧ moments m leaf 1=(m+1)*mu1 m ∧
    moments m leaf 2=(m+1)*mu2 m ∧ moments m leaf 3=(m+1)*mu3 m := by
  have hh := sum_powers m
  simp only [leaf,moments,moment,configFintype,deficit,population,Lift,liftDef,
    Fintype.sum_sigma, Nat.add_zero, Fintype.sum_unique, pow_zero,
    pow_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Fintype.card_sigma, Fintype.card_unit,
    nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]
  rcases hh with ⟨h1,h2,h3⟩
  rw [h1,h2,h3]
  simp only [mu1,mu2,mu3,Fintype.card_unit,Nat.cast_one,one_mul]
  constructor
  · simp
  constructor
  · ring
  constructor <;> ring

def starP (k : ℕ) (m : ℚ) := m+1+s1 k m
def starD (k : ℕ) (m : ℚ) := (m*(m+1)+(2*m+1)*s1 k m+s2 k m)/2
def starW (k : ℕ) (m : ℚ) :=
  (2*m^3+3*m^2+m+(6*m^2+6*m+1)*s1 k m+(6*m+3)*s2 k m+2*s3 k m)/6

theorem star_moments (m k : ℕ) :
    moments m (star k) 0=(m+1)^k*starP k m ∧
    moments m (star k) 1=(m+1)^k*starD k m ∧
    moments m (star k) 2=(m+1)^k*starW k m := by
  rcases leaf_moments m with ⟨h0,h1,h2,h3⟩
  rcases copies_moments m k leaf (m+1) (mu1 m) (mu2 m) (mu3 m) h0 h1 h2 h3 with
    ⟨r0,r1,r2,r3⟩
  simp only [star,root_moments0,root_moments1,root_moments2,r0,r1,r2,r3,
    starP,starD,starW,s1,s2,s3]
  constructor
  · ring
  constructor <;> ring

theorem copies_ten_moments (m : ℕ) (f : Forest) :
    moments m (copies f 10) 0=(moments m f 0)^10 ∧
    moments m (copies f 10) 1=10*(moments m f 0)^9*moments m f 1 ∧
    moments m (copies f 10) 2=10*(moments m f 0)^9*moments m f 2+
      90*(moments m f 0)^8*(moments m f 1)^2 := by
  simp only [copies,pair_moments0,pair_moments1,pair_moments2,
    moments_empty0,moments_empty_pos]
  constructor
  · ring
  constructor <;> ring

theorem two_roots (m : ℕ) (f : Forest) :
    moments m (root (root f)) 0=
      ((m+1)*(3*m+2)*moments m f 0+(4*m+3)*moments m f 1+moments m f 2)/2 := by
  rw [root_moments0,root_moments0,root_moments1]
  ring

def core (m P D W Q d w : ℚ) :=
  ((m+1)*(3*m+2)*(P*Q^2)+(4*m+3)*(D*Q^2+10*P*Q*d)+
    W*Q^2+10*P*Q*w+90*P*d^2+20*D*d*Q)/2

theorem forest_factor (m h P D W Q d w : ℚ) :
    ((m+1)*(3*m+2)*((h^180*P)*(h^5*Q)^10)+
     (4*m+3)*((h^180*D)*(h^5*Q)^10+(h^180*P)*(10*(h^5*Q)^9*(h^5*d)))+
     ((h^180*W)*(h^5*Q)^10+2*(h^180*D)*(10*(h^5*Q)^9*(h^5*d))+
       (h^180*P)*(10*(h^5*Q)^9*(h^5*w)+90*(h^5*Q)^8*(h^5*d)^2)))/2 =
    h^230*(Q^8*core m P D W Q d w) := by
  unfold core
  ring

def fQ (m : ℚ) := 24+5852*m+400056*m^2+8533751*m^3+44368122*m^4+67184474*m^5
def Eeval (m : ℚ) := (m+1)^230*((7*m+2)^8*fQ m/6144)

theorem core_witness (m : ℚ) :
    core m (starP 180 m) (starD 180 m) (starW 180 m)
      (starP 5 m) (starD 5 m) (starW 5 m)=fQ m/24 := by
  norm_num [core,starP,starD,starW,s1,s2,s3,mu1,mu2,mu3,fQ]
  ring

theorem small_factor (m : ℚ) : (starP 5 m)^8*(fQ m/24)=(7*m+2)^8*fQ m/6144 := by
  norm_num [starP,s1,mu1]
  ring

/-- An all-dilation lattice-count theorem for the explicit 243-vertex arbor.
The left side counts actual coordinate tuples satisfying all subtree bounds. -/
theorem witness_count (m : ℕ) :
    (Nat.card {x : Coord witness // Valid m witness x} : ℚ)=Eeval m := by
  rw [lattice_count_eq_moment]
  unfold witness
  rw [two_roots,pair_moments0,pair_moments1,pair_moments2]
  rcases copies_ten_moments m (star 5) with ⟨r0,r1,r2⟩
  rw [r0,r1,r2]
  rcases star_moments m 180 with ⟨a0,a1,a2⟩
  rcases star_moments m 5 with ⟨b0,b1,b2⟩
  rw [a0,a1,a2,b0,b1,b2,forest_factor,core_witness,small_factor]
  rfl

#print axioms witness_count

end Forest
end
end ArborCounterexample
