import Algorithm.Poly.cPoly

abbrev nPoly (R : Type _) [Semiring R] := {F : cPoly R // cPoly.normalized F}
variable {R : Type _} [Semiring R]
instance : Coe (nPoly R) (cPoly R) := ⟨Subtype.val⟩
open Polynomial

namespace nPoly

noncomputable def toPolynomial (F : nPoly R) : R[X] := F.1.toPolynomial
noncomputable def ofPolynomial (F : R[X]) : nPoly R :=
  ⟨cPoly.ofPolynomial F, cPoly.ofPolynomial_normalized F⟩
end nPoly

noncomputable def equivPolynomial:
    nPoly R ≃ R[X] where
  toFun := nPoly.toPolynomial
  invFun := nPoly.ofPolynomial
  left_inv := sorry
  right_inv := sorry
