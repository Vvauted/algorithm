import Mathlib

abbrev vPoly (R : Type _) (n : Nat) := Vector R n
variable {R : Type _} [Ring R]

namespace Polynomial

noncomputable def trunc (F : R[X]) (n : ℕ) : R[X] := F %ₘ (X ^ n)

noncomputable def trunc_coeff (F : R[X]) (n : ℕ) : ℕ → R :=
  fun i => if i < n then F.coeff i else 0

@[simp]
lemma trunc_coeff_is_Finsupp (F : R[X]) (n : ℕ) :
   ∀ (a : ℕ), F.trunc_coeff n a ≠ 0 → a ∈ Finset.range n := by
    unfold trunc_coeff
    simp only [ne_eq, ite_eq_right_iff, Classical.not_imp, Finset.mem_range, and_imp]
    intros o p q
    exact p

noncomputable def trunc_toFinsupp (F : R[X]) (n : ℕ) : ℕ →₀ R :=
  Finsupp.onFinset (Finset.range n) (trunc_coeff F n) (trunc_coeff_is_Finsupp F n)

@[simp]
lemma trunc_coeff_eq (F : R[X]) (n : ℕ) : trunc_coeff F n i = (trunc F n).coeff i := by
  unfold trunc trunc_coeff
  have p := modByMonic_add_div (q := X ^ n) F (by simp)
  sorry

@[simp]
lemma trunc_toFinsupp_eq_trunc (F : R[X]) (n : ℕ) :
  Polynomial.ofFinsupp (trunc_toFinsupp F n) = trunc F n := by
  unfold trunc_toFinsupp
  ext i
  simp only [coeff_ofFinsupp, Finsupp.onFinset_apply]
  exact trunc_coeff_eq F n

@[simp]
lemma trunc_eq_finsum (F : R[X]) (n : ℕ) :
  trunc F n = ∑ i : Fin n, C (F.coeff i) * X ^ (i : ℕ) := by
  ext i
  rw [← trunc_coeff_eq]
  unfold trunc_coeff
  simp only [finset_sum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Fin.sum_univ_eq_sum_range (fun x => if i = ↑x then F.coeff ↑x else 0)]
  simp only [Finset.sum_ite_eq, Finset.mem_range]

end Polynomial

open Polynomial

namespace vPoly

def coeff (F : vPoly R n) (x : ℕ) : R :=
  if p : x < n then F[x] else 0

@[simp]
lemma coeff_vPoly_is_Finsupp (F : vPoly R n) :
  (∀ (a : ℕ), F.coeff a ≠ 0 → a ∈ Finset.range n) := by
  unfold coeff
  simp only [ne_eq, dite_eq_right_iff, not_forall, Finset.mem_range, forall_exists_index]
  intros o p q
  exact p

noncomputable def toFinsupp (F : vPoly R n) : ℕ →₀ R :=
  Finsupp.onFinset (Finset.range n) (coeff F) (coeff_vPoly_is_Finsupp F)

noncomputable def toPolynomial (F : vPoly R n) : R[X] :=
  Polynomial.ofFinsupp F.toFinsupp

noncomputable def toPolynomial_Sum (F : vPoly R n) : R[X] :=
  ∑ i : Fin n, C F[i] * X ^ (i : ℕ)

def ofPolynomial_trunc (p : R[X]) (n : ℕ) : vPoly R n :=
  Vector.ofFn fun (i : Fin n) => p.coeff (i : ℕ)

@[simp]
lemma ofPolynomial_toPolynomial_Sum_eq_self_trunc (F : R[X]) :
   (vPoly.ofPolynomial_trunc F n).toPolynomial_Sum = trunc F n := by
  unfold vPoly.ofPolynomial_trunc vPoly.toPolynomial_Sum
  dsimp; simp only [Vector.getElem_ofFn]; symm
  exact trunc_eq_finsum F n


@[simp]
lemma ofPolynomial_toPolynomial_eq_self (F : R[X]) (n : ℕ) :
   (vPoly.ofPolynomial_trunc F n).toPolynomial = trunc F n := by
  unfold vPoly.ofPolynomial_trunc vPoly.toPolynomial vPoly.toFinsupp vPoly.coeff
  ext i
  simp only [Vector.getElem_ofFn, dite_eq_ite, coeff_ofFinsupp, Finsupp.onFinset_apply]
  exact trunc_coeff_eq F n

end vPoly
