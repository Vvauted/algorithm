import Mathlib.Algebra.Polynomial.Degree.Support

abbrev cPoly (R : Type _) := Array R
variable {R : Type _} [Semiring R]
open Polynomial

namespace cPoly

def coeff (F : cPoly R) (n : ℕ) : R :=
  if p : n < F.size then F[n] else 0

lemma coeff_cPoly_is_Finsupp (F : cPoly R) :
  (∀ (a : ℕ), F.coeff a ≠ 0 → a ∈ Finset.range F.size) := by
  unfold coeff
  simp only [ne_eq, dite_eq_right_iff, not_forall, Finset.mem_range, forall_exists_index]
  intros o p q
  exact p

noncomputable def toFinsupp (F : cPoly R) : ℕ →₀ R :=
  Finsupp.onFinset (Finset.range F.size) (coeff F) (coeff_cPoly_is_Finsupp F)

noncomputable def toPolynomial (F : cPoly R) : R[X] :=
  Polynomial.ofFinsupp F.toFinsupp

noncomputable def toPolynomial_Sum (F : cPoly R) : R[X] :=
  ∑ i : Fin F.size, C F[i] * X ^ (i : ℕ)

def ofPolynomial (p : R[X]) : cPoly R :=
  p.degree.recBotCoe #[] fun x => Array.ofFn fun (i : Fin (x + 1)) => p.coeff (i : ℕ)

def normalized (F : cPoly R) : Prop :=
  (p : F.size > 0) → F[F.size - 1] ≠ 0

@[simp]
lemma of_Polynomial_inj (F G : R[X]) : ofPolynomial F = ofPolynomial G → F = G := by
  unfold ofPolynomial
  cases hF : F.degree with
  | bot =>
    cases hG : G.degree with
    | bot =>
      simp only [degree_eq_bot] at hF hG
      simp only [WithBot.recBotCoe_bot, forall_const]
      rw [hF, hG]
    | coe y => simp
  | coe x =>
    cases hG : G.degree with
    | bot => simp
    | coe y =>
      simp only [WithBot.recBotCoe_coe]
      intro p
      simp only [Array.ext_iff, Array.size_ofFn, Nat.add_right_cancel_iff, Order.lt_add_one_iff,
        Array.getElem_ofFn] at p
      rcases p with ⟨hl, hr⟩
      simp only [← hl, forall_self_imp] at hr hl hG hF
      ext i
      by_cases hi : i <= x
      · apply hr; exact hi
      · simp at hi
        apply natDegree_eq_of_degree_eq_some at hF
        apply natDegree_eq_of_degree_eq_some at hG
        rw [coeff_eq_zero_of_natDegree_lt (by omega)]
        rw [coeff_eq_zero_of_natDegree_lt (by omega)]

@[simp]
lemma ofPolynomial_toPolynomial_Sum_eq_self (F : R[X]) :
   (cPoly.ofPolynomial F).toPolynomial_Sum = F := by
  unfold cPoly.ofPolynomial cPoly.toPolynomial_Sum
  cases h : F.degree with
  | bot =>
    simp at h
    simp [Array.size_empty, h]
  | coe x =>
    dsimp; simp only [Array.getElem_ofFn];
    conv_rhs => rw [F.as_sum_range_C_mul_X_pow]
    rw [Fin.sum_univ_eq_sum_range (fun x ↦ C (F.coeff x) * X ^ x)]
    simp only [Array.size_ofFn, natDegree]
    apply Finset.sum_congr_of_eq_on_inter
    · simp +contextual [h]
    · simp +contextual [h]
    · simp

@[simp]
lemma ofPolynomial_toPolynomial_eq_self (F : R[X]) :
   (cPoly.ofPolynomial F).toPolynomial = F := by
  unfold cPoly.ofPolynomial cPoly.toPolynomial cPoly.toFinsupp cPoly.coeff
  ext i
  cases h : F.degree with
  | bot =>
    simp only [degree_eq_bot] at h
    simp only [h, coeff_zero, WithBot.recBotCoe_bot,
    List.size_toArray, List.length_nil, Finset.range_zero, not_lt_zero, ↓reduceDIte,
    coeff_ofFinsupp, Finsupp.onFinset_apply]
  | coe x =>
    simp only [WithBot.recBotCoe_coe, Array.size_ofFn, Order.lt_add_one_iff, Array.getElem_ofFn,
      dite_eq_ite, coeff_ofFinsupp, Finsupp.onFinset_apply, ite_eq_left_iff, not_le]
    intro p; symm
    apply natDegree_eq_of_degree_eq_some at h
    rw [← h] at p
    exact coeff_eq_zero_of_natDegree_lt p

lemma toPolynomial_eq_toPolynomial_sum (F : cPoly R) : toPolynomial F = toPolynomial_Sum F := by
  unfold toPolynomial toPolynomial_Sum toFinsupp coeff
  ext i; symm
  simp only [Fin.getElem_fin, finset_sum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one,
    mul_zero, coeff_ofFinsupp, Finsupp.onFinset_apply]
  split_ifs with hp
  · simp only [ite_eq_dite]
    conv =>
      enter [1, 2, x, 2, h]
      simp [← h]
      skip
    rw [Fin.sum_univ_eq_sum_range (fun x => if h : i = ↑x then F[i] else 0)]
    simp only [dite_eq_ite, Finset.sum_ite_eq, Finset.mem_range, hp, ↓reduceIte]
  · simp at hp
    refine Finset.sum_eq_zero ?_
    simp only [Finset.mem_univ, ite_eq_right_iff, forall_const]
    intro x hx
    omega

@[simp]
lemma ofPolynomial_normalized : ∀ F : R[X], (cPoly.ofPolynomial F).normalized := by
  unfold cPoly.ofPolynomial cPoly.normalized
  intro F
  cases h : F.degree with
  | bot =>
    simp only [degree_eq_bot] at h
    simp only [h, coeff_zero, WithBot.recBotCoe_bot, List.size_toArray, List.length_nil, gt_iff_lt,
      lt_self_iff_false, zero_tsub, List.getElem_toArray, ne_eq, IsEmpty.forall_iff]
  | coe x =>
    simp only [WithBot.recBotCoe_coe, Array.size_ofFn, gt_iff_lt, lt_add_iff_pos_left,
      Order.lt_add_one_iff, zero_le, add_tsub_cancel_right, Array.getElem_ofFn, ne_eq, forall_const]
    exact coeff_ne_zero_of_eq_degree h

lemma toPolynomial_coeff_eq_self_coeff (F : cPoly R) : F.toPolynomial.coeff = F.coeff := by
  unfold toPolynomial toFinsupp
  simp

end cPoly
