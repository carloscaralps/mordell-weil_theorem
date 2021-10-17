import algebraic_geometry.EllipticCurve

open EllipticCurve

def non_projective_points {R : Type*} [comm_ring R] (E : EllipticCurve R) :=
  { x : R × R | x.2^2+E.a1*x.1*x.2+E.a3*x.2 = x.1^3+E.a2*x.1^2+E.a4*x.1+E.a6 }

localized "notation `non_P` := non_projective_points" in EllipticCurve

#check prod

def operation_non_P {R : Type*} [comm_ring R] (E : EllipticCurve R) : non_P E → non_P E → non_P E :=
begin
  intros x y,
  let γ : R := begin 
    
    --else exact x.1.1
    sorry end, 
  let t₁ := γ*γ - E.a2-x.1.1-y.1.1,
  let t₂ := γ*(x.1.1-t₁)-x.1.2,
  use ⟨t₁, t₂⟩,
  have : t₂^2+E.a1*t₁*t₂+E.a3*t₂ = t₁^3+E.a2*t₁^2+E.a4*t₁+E.a6,
  {
    sorry
  },
  exact this,
end

def defined_points {R : Type*} [comm_ring R] (E : EllipticCurve R) := 
  option (non_P E)

localized "notation `E` := defined_points" in EllipticCurve

variables {R : Type*} [comm_ring R] (L : EllipticCurve R)

def non_projective_points_to_defined_points : non_P L → E L := λ x, some x

def pints_comm_group : comm_group (E L) :=
{ mul := 
  begin
    intros x y,
    cases x,
    { exact y },
    { cases y,
      { exact some x },
      { exact (some (operation_non_P L x y)) } }  
  end,
  mul_assoc := sorry,
  one := sorry,
  one_mul := sorry,
  mul_one := sorry,
  npow := sorry,
  npow_zero' := sorry,
  npow_succ' := sorry,
  inv := sorry,
  div := sorry,
  div_eq_mul_inv := sorry,
  gpow := sorry,
  gpow_zero' := sorry,
  gpow_succ' := sorry,
  gpow_neg' := sorry,
  mul_left_inv := sorry,
  mul_comm := sorry }
