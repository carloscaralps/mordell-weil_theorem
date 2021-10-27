import algebraic_geometry.EllipticCurve

namespace our_EllipticCurve

structure our_EllipticCurve (F: Type) [field F] :=
(a2 a4 a6 : F)
(disc_unit : EllipticCurve.disc_aux 0 a2 0 a4 a6 ≠ 0)

variables {F: Type} [decidable_eq F][field F]

def non_projective_points (E : our_EllipticCurve F) :=
  { x : F × F | x.2^2 = x.1^3+E.a2*x.1^2+E.a4*x.1+E.a6 }

localized "notation `non_P` := non_projective_points" in EllipticCurve

def defined_points (E : our_EllipticCurve F) :=
  option (non_P E)

instance (E : our_EllipticCurve F): has_zero (defined_points E) :=
{ zero := none }

def group_law (E : our_EllipticCurve F):  defined_points E →  defined_points E → defined_points E
 | 0 P := P
 | P 0 := P
 | (some ⟨⟨x,y⟩, h⟩) (some ⟨⟨x',y'⟩, h'⟩) :=
   if (x = x') ∧ ((y : F) ≠ (y' : F)) then 0 else
    if (x = x') ∧ (y = y') then 
      sorry -- tangent construction
    else 
      sorry -- secant construction

instance has_add (E : our_EllipticCurve F): has_add (defined_points E) :=
  { add :=  group_law E }

end our_EllipticCurve