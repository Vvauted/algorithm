import Algorithm.Poly.cPoly

abbrev nPoly (R : Type _) [Semiring R] := {F : cPoly R // cPoly.normalized F}
variable {R : Type _} [Semiring R]
instance : Coe (nPoly R) (cPoly R) := ⟨Subtype.val⟩
open Polynomial

namespace nPoly

noncomputable def toPolynomial (F : nPoly R) : R[X] := F.1.toPolynomial

noncomputable def ofPolynomial (F : R[X]) : nPoly R :=
  ⟨cPoly.ofPolynomial F, cPoly.ofPolynomial_normalized F⟩

noncomputable def coeff (F : nPoly R) : ℕ → R := F.1.coeff

lemma toPolynomial_coeff_eq_self_coeff (F : nPoly R) :
  F.toPolynomial.coeff = F.coeff := F.1.toPolynomial_coeff_eq_self_coeff

@[simp]
lemma toPolynomial_inj (F G : nPoly R) : F.toPolynomial = G.toPolynomial → F = G := by
  unfold toPolynomial
  repeat rw [cPoly.toPolynomial_eq_toPolynomial_sum]
  unfold cPoly.toPolynomial_Sum
  intro hs
  sorry

@[simp]
lemma ofPolynomial_toPolynomial_eq_self (F : R[X]) :
   (ofPolynomial F).toPolynomial = F := by
   exact cPoly.ofPolynomial_toPolynomial_eq_self F

end nPoly

noncomputable def nPolyequivPolynomial :
    nPoly R ≃ R[X] where
  toFun := nPoly.toPolynomial
  invFun := nPoly.ofPolynomial
  left_inv := by
    unfold Function.LeftInverse
    intro F
    apply nPoly.toPolynomial_inj
    simp
  right_inv := by
    unfold Function.RightInverse Function.LeftInverse
    exact cPoly.ofPolynomial_toPolynomial_eq_self
