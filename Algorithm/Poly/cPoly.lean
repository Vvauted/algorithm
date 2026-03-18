import Mathlib

abbrev cPoly (R : Type _) := Array R
variable {R : Type _} [Semiring R]
open Polynomial

namespace cPoly

noncomputable def toPolynomial (F : cPoly R) : R[X] :=
  ∑ i : Fin F.size, C F[i] * X ^ (i : ℕ)

def ofPolynomial (p : R[X]) : cPoly R :=
  let d := p.natDegree
  Array.ofFn fun (i : Fin (d + 1)) => p.coeff (i : ℕ)

end cPoly

lemma ofPolynomial_toPolynomial_eq_self (F : R[X]) : (cPoly.ofPolynomial F).toPolynomial = F := by
  unfold cPoly.ofPolynomial cPoly.toPolynomial
  simp only [Lean.Elab.WF.paramLet, Fin.getElem_fin, Array.getElem_ofFn]
  ext i
  simp only [finset_sum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  simp [Finset.sum_ite_eq]


  conv_lhs =>
    arg 2; ext; rw [ite_eq_dite]
    arg 2; intro h; rw [← h]
  simp only [dite_eq_ite]


  norm_cast
