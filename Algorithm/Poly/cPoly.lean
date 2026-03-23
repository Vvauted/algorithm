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

@[simp]
lemma ofPolynomial_toPolynomial_eq_self (F : R[X]) : (cPoly.ofPolynomial F).toPolynomial = F := by
  unfold cPoly.ofPolynomial cPoly.toPolynomial
  simp only [Lean.Elab.WF.paramLet, Fin.getElem_fin, Array.getElem_ofFn]
  conv_rhs => rw [F.as_sum_range_C_mul_X_pow]
  rw [Fin.sum_univ_eq_sum_range (fun x ↦ C (F.coeff x) * X ^ x)]
  apply Finset.sum_congr_of_eq_on_inter
  · simp +contextual
  · simp +contextual
  · simp
