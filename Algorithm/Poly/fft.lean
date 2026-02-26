import Mathlib

abbrev biPoly (R : Type _) (k : Nat) := Vector R (2 ^ k)
variable {R : Type _} [CommRing R]

def poly_eval (f : biPoly R k) (x : R) : R :=
  ∑ i : Fin (2 ^ k), f[i] * x ^ i.val

def even (f : biPoly R (k + 1)) : biPoly R k :=
  Vector.ofFn fun i => f[2 * i.val]

def odd (f : biPoly R (k + 1)) : biPoly R k :=
  Vector.ofFn fun i => f[2 * i.val + 1]

def spilt_L (f : biPoly R (k + 1)) : biPoly R k :=
  Vector.ofFn fun i => f[i]

def calc_W (k : Nat) (ω : R) : biPoly R k :=
  Vector.ofFn fun i => ω ^ i.val

def proot_inv (ω : R) (k : ℕ) : R := ω ^ (2 ^ k - 1)

def dft (f : biPoly R k) (ω : R) : biPoly R k :=
  (calc_W k ω).map fun x => poly_eval f x

def idft (f : biPoly R k) (ω : R)
  [inv : Invertible (2 ^ k : R)] : biPoly R k :=
      (dft f (proot_inv ω k)).map fun x => x * ⅟(2 ^ k: R)

def poly_get (f : biPoly R k) (i : ℕ) : R :=
  if w : i < 2 ^ k then f[i]
  else 0

def extend (f : biPoly R k) : biPoly R (k + 1) :=
  Vector.ofFn fun i => poly_get f i

def mul (F : biPoly R k) (G : biPoly R k) : biPoly R (k + 1) :=
  Vector.ofFn fun i =>
    ∑ j : Fin (2 ^ k), ∑ k : Fin (2 ^ k), if j.val + k.val = i then F[j] * G[k] else 0

def _fft (f : biPoly R k) (W : biPoly R k) : biPoly R k :=
  match k with
  | 0 => f
  | k + 1 =>
    let Wp := even W
    let fE : biPoly R k := _fft (even f) Wp
    let fO : biPoly R k :=  _fft (odd f) Wp
    let W₂fO := Vector.zipWith (· * ·) (spilt_L W) fO
    let l := (Vector.zipWith (· + ·) fE W₂fO)
    let r := (Vector.zipWith (· - ·) fE W₂fO)
    Vector.cast (by simp) l ++ r

def fft (f : biPoly R k) (ω : R) : biPoly R k :=
  _fft f (calc_W k ω)

lemma proot_inv_is_proot (ω : R) (hω : IsPrimitiveRoot ω (2 ^ k)) :
  IsPrimitiveRoot (proot_inv ω k) (2 ^ k) := by
    unfold proot_inv
    simp [IsPrimitiveRoot.pow_iff_coprime hω]
    have p : (1 ≤ 2 ^ k) := by exact Nat.one_le_two_pow
    simp [Nat.coprime_self_sub_left p]

def ifft (f : biPoly R k) (ω : R)
  [inv : Invertible (2 ^ k : R)] : biPoly R k :=
    let g := fft f (proot_inv ω k)
    g.map fun x => x * ⅟(2 ^ k : R)

def fin_even_odd_equiv (k : ℕ) : Fin (2 ^ k) ⊕ Fin (2 ^ k) ≃ Fin (2 ^ (k + 1)) where
  toFun x := match x with
    | Sum.inl i => ⟨i.val * 2, by omega⟩
    | Sum.inr i => ⟨i.val * 2 + 1, by omega⟩
  invFun i :=
    if i.val % 2 = 0
    then Sum.inl ⟨i.val / 2, by omega⟩
    else Sum.inr ⟨i.val / 2, by omega⟩
  left_inv x := by
    cases x
    · dsimp
      split_ifs with p
      · simp
      · omega
    · dsimp
      split_ifs with p
      · omega
      · congr; omega
  right_inv i := by
    cases i
    · dsimp
      split_ifs with p
      · simp; omega
      · simp; omega

lemma poly_parity_split (f : biPoly R (k + 1)) :
  poly_eval (even f) (x ^ 2) + x * poly_eval (odd f) (x ^ 2) = poly_eval f x
  := by
    unfold poly_eval
    have pE (i) (_ : i < 2 ^ k) : (even f)[i] = f[2 * i] := by
      unfold even
      simp only [Vector.getElem_ofFn]
    have pO (i) (_ : i < 2 ^ k) : (odd f)[i] = f[2 * i + 1] := by
      unfold odd
      simp only [Vector.getElem_ofFn]
    simp only [Fin.getElem_fin, pE, pO]
    simp only [← pow_mul, Finset.mul_sum]
    simp only [← mul_assoc, ← mul_comm, ← pow_succ']
    simp [← Equiv.sum_comp (fin_even_odd_equiv k), fin_even_odd_equiv]

lemma W_sq_eq_next {ω : R} (hω : IsPrimitiveRoot ω (2 ^ (k + 1))) :
  IsPrimitiveRoot (ω ^ 2) (2 ^ k) := by
    exact IsPrimitiveRoot.pow (by exact Nat.two_pow_pos (k + 1)) hω (by omega)

lemma even_W_eq_sq (ω : R) :
  even (calc_W (k + 1) ω) = calc_W k (ω ^ 2) := by
    unfold even calc_W
    ext i
    simp only [Vector.getElem_ofFn]
    exact pow_mul ω 2 i

lemma proot_halfpow_eq_neg_one [IsDomain R] (ω : R) (hω : IsPrimitiveRoot ω (2 ^ (k + 2))) :
  ω ^ (2 ^ (k + 1)) = -1 := by
    have c : 2 ^ (k + 1) ≠ 0 := by exact Ne.symm (NeZero.ne' (2 ^ (k + 1)))
    have e : (k + 1) ≤ (k + 2) := by omega
    have ty : 1 < 2 := by omega
    have p : 2 ^ (k + 1) ∣ 2 ^ (k + 2) := by exact (Nat.pow_dvd_pow_iff_le_right ty).mpr e
    exact IsPrimitiveRoot.eq_neg_one_of_two_right (by
      convert IsPrimitiveRoot.pow_of_dvd hω c p; exact Nat.eq_div_of_mul_eq_right c rfl)


theorem fft_eq_dft [IsDomain R] (f : biPoly R k) (ω : R) (hω : IsPrimitiveRoot ω (2 ^ k)) :
  fft f ω = dft f ω := by
  rw [fft, dft]
  ext i L
  simp only [Vector.getElem_map]
  conv_rhs => simp [Vector.ofFn]
  induction k generalizing ω i with
    | zero =>
      simp only [Nat.pow_zero, calc_W, Fin.val_eq_zero, pow_zero, Vector.getElem_ofFn]
      unfold _fft poly_eval
      simp only [Nat.pow_zero, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
        Fin.val_eq_zero, pow_zero, mul_one, Finset.sum_singleton, Fin.getElem_fin]
      interval_cases i
      rfl
    | succ k p =>
      unfold _fft
      have q : IsPrimitiveRoot (ω ^ 2) (2 ^ k):= W_sq_eq_next hω
      by_cases h : i < (2 ^ k)
      · erw [Vector.getElem_append_left h]
        simp only [Vector.getElem_zipWith]
        unfold spilt_L
        simp only [Vector.getElem_ofFn]
        rw [even_W_eq_sq]
        · simp only [q, p, Fin.getElem_fin]
          simp only [calc_W, Vector.getElem_ofFn]
          rw [pow_right_comm]
          apply poly_parity_split
      · have rh : 2 ^ k ≤ i := by omega
        erw [Vector.getElem_append_right L (by simp; omega)]
        simp only [Nat.pow_eq, Nat.mul_eq, mul_one, Vector.getElem_zipWith]
        unfold spilt_L
        simp only [Fin.getElem_fin, Vector.getElem_ofFn]
        simp only [even_W_eq_sq]
        simp only [q, p]
        simp only [calc_W, Vector.getElem_ofFn]
        rw [pow_right_comm]
        have pω : - ω ^ (2 ^ k) = 1 := by
          apply neg_eq_iff_eq_neg.mpr
          cases k
          · simp only [pow_zero, pow_one]
            exact IsPrimitiveRoot.eq_neg_one_of_two_right hω
          · exact proot_halfpow_eq_neg_one ω hω
        rw [← mul_one (ω ^ (i - 2 ^ k))]
        simp only [← pω, mul_neg, ← pow_add, Nat.sub_add_cancel rh, even_two, Even.neg_pow,
        neg_mul, sub_neg_eq_add]
        apply poly_parity_split

theorem ifft_eq_idft [IsDomain R] [p : Invertible (2 ^ k : R)] (f : biPoly R k)
  (hω : IsPrimitiveRoot ω (2 ^ k)) : (ifft f ω) = idft f ω := by
    unfold ifft idft
    ext i
    simp only [Vector.getElem_map]
    rw [fft_eq_dft]
    exact proot_inv_is_proot ω hω

theorem sum_pow_ {ω : R} [IsDomain R] (hω : IsPrimitiveRoot ω (2 ^ k)) (i : ℕ) :
    ∑ j ∈ .range (2 ^ k), (ω ^ i) ^ j = if 2 ^ k ∣ i then 2 ^ k else 0 := by
  split_ifs with hi <;> rw [← hω.pow_eq_one_iff_dvd] at hi
  · simp [hi]
  · rw [← mul_left_inj' (sub_ne_zero.mpr hi), geom_sum_mul, pow_right_comm, hω.pow_eq_one]; simp

theorem dft_idft_eq_self [IsDomain R] [p : Invertible (2 ^ k : R)]
  (hω : IsPrimitiveRoot ω (2 ^ k)) (f : biPoly R k) : dft (idft f ω) ω = f := by
    simp only [dft, poly_eval, idft, Fin.getElem_fin, calc_W, proot_inv, Vector.map_map,
      Vector.getElem_map, Vector.getElem_ofFn, Function.comp_apply]
    ext i hi
    simp only [Finset.sum_mul, Vector.getElem_map, Vector.getElem_ofFn]
    rw [Finset.sum_comm]
    simp only [mul_assoc, mul_left_comm _ (⅟(2 ^ k : R))]
    simp only [← pow_mul, ← pow_add, ← Finset.mul_sum]
    simp_rw [mul_right_comm, ← add_mul, pow_mul, Fin.sum_univ_eq_sum_range]
    calc
      _ = ⅟(2 ^ k : R) * ∑ (j1 : Fin (2 ^ k)), f[(j1 : ℕ)] * if j1 = i then 2 ^ k else 0 := by
        congr! with j1
        rw [sum_pow_ hω]; congr; ext; zify
        rw [Nat.cast_sub Nat.one_le_two_pow, sub_mul, sub_eq_add_neg, add_assoc]
        constructor <;> simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, one_mul,
          Int.dvd_self_mul_add, Nat.cast_inj]
        · rw [neg_eq_zero_sub, sub_add]; simp only [zero_sub, neg_sub]
          intro u; apply Nat.modEq_of_dvd at u
          exact Nat.ModEq.eq_of_lt_of_lt u j1.isLt hi
        · intro u; simp [u];
      _ = ⅟(2 ^ k : R) * ∑ (j1 : Fin (2 ^ k)), if j1 = i then f[i] * 2 ^ k else 0 := by
        congr! 2 with j1
        split_ifs with h <;> simp [h]
      _ = f[i] := by
        simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul]
        rw [Finset.card_eq_one.mpr ⟨⟨i, hi⟩, by ext; simp [Fin.ext_iff]⟩]
        simp [mul_comm]

theorem idft_dft_eq_self [IsDomain R] [p : Invertible (2 ^ k : R)]
  (hω : IsPrimitiveRoot ω (2 ^ k)) (f : biPoly R k) : idft (dft f ω) ω = f := by
    simp only [idft, dft, poly_eval, Fin.getElem_fin, calc_W, Vector.getElem_map,
      Vector.getElem_ofFn, proot_inv, Vector.map_map]
    ext i hi
    simp only [Vector.getElem_map, Vector.getElem_ofFn, Function.comp_apply]
    conv =>
      enter [1, 1]
      simp [Finset.sum_mul]
      rw [Finset.sum_comm]
      rw [← pow_mul]
      simp only [mul_assoc, mul_left_comm _ (⅟(2 ^ k : R))]
      simp only [← pow_mul, ← pow_add, ← Finset.mul_sum]
      skip
    conv =>
      enter [1, 1, 2, x, 2, 2, i]
      rw [mul_comm]
      rw [← add_mul]
      rw [pow_mul]
      skip
    simp_rw [Fin.sum_univ_eq_sum_range]
    rw [mul_comm]
    calc
      _ = ⅟(2 ^ k : R) * ∑ (j1 : Fin (2 ^ k)), f[(j1 : ℕ)] * if j1 = i then 2 ^ k else 0 := by
        congr! with j1
        rw [sum_pow_ hω]
        congr
        ext
        zify
        rw [Nat.cast_sub Nat.one_le_two_pow, sub_mul, sub_eq_add_neg]
        simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, one_mul, Nat.cast_inj]
        simp only [add_comm, ← add_assoc, Int.dvd_add_self_mul]
        rw [Int.add_neg_eq_sub]
        constructor
        · intro u; apply Nat.modEq_of_dvd at u; symm
          exact Nat.ModEq.eq_of_lt_of_lt u hi j1.isLt
        · intro u; simp [u];
      _ = ⅟(2 ^ k : R) * ∑ (j1 : Fin (2 ^ k)), if j1 = i then f[i] * 2 ^ k else 0 := by
        congr! 2 with j1
        split_ifs with h <;> simp [h]
      _ = f[i] := by
        simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul]
        rw [Finset.card_eq_one.mpr ⟨⟨i, hi⟩, by ext; simp [Fin.ext_iff]⟩]
        simp [mul_comm]

theorem fft_ifft_eq_self [IsDomain R] [p : Invertible (2 ^ k : R)]
  (hω : IsPrimitiveRoot ω (2 ^ k)) (f : biPoly R k) : fft (ifft f ω) ω = f := by
    simp only [fft_eq_dft, ifft_eq_idft, dft_idft_eq_self, hω]


theorem ifft_fft_eq_self [IsDomain R] [p : Invertible (2 ^ k : R)]
  (hω : IsPrimitiveRoot ω (2 ^ k)) (f : biPoly R k) : ifft (fft f ω) ω = f := by
    simp only [hω, fft_eq_dft, ifft_eq_idft, idft_dft_eq_self]

def mul_fft [IsDomain R] [p : Invertible (2 ^ (k + 1) : R)]
   (F : biPoly R k) (G : biPoly R k) (ω : R) : biPoly R (k + 1) :=
    let (F', G') := (extend F, extend G)
    let (Fp, Gp) := (fft F' ω, fft G' ω)
    let FGp := Vector.zipWith (· * ·) Fp Gp
    ifft FGp ω

theorem eval_mul_eq_mul_eval (f : biPoly R k) (g : biPoly R k) (x : R) :
  poly_eval (mul f g) x = poly_eval f x * poly_eval g x := by
  unfold mul
  simp only [poly_eval, Fin.getElem_fin, Vector.getElem_ofFn]
  simp only [Fintype.sum_mul_sum]
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  conv => enter [1, 2, y]; rw [Finset.sum_comm]; skip
  simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  simp only [← Finset.mul_sum]
  have p (x : Fin (2 ^ k)) (y : Fin (2 ^ k)) : x.val + y.val < 2 ^ (k + 1) := by omega
  simp_rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro px ppx
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro py ppy
  simp only [← Finset.mul_sum]
  rw [Finset.sum_eq_single ⟨↑px + ↑py, by omega⟩]
  · simp only [↓reduceIte, pow_add]; ring
  · simp only [Finset.mem_univ, ne_eq, ite_eq_right_iff, forall_const]
    intro pb pc pd; exfalso; apply pc;
    apply Fin.eq_of_val_eq
    rw [← pd]
  · simp

theorem extend_eq_self (F : biPoly R k) (x : R) :  (poly_eval (extend F) x) = (poly_eval F x):= by
  unfold poly_eval extend
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, poly_get]
  rw [Finset.sum_fin_eq_sum_range]
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr_of_eq_on_inter <;> grind

theorem mul_fft_eq_mul [IsDomain R] [p : Invertible (2 ^ (k + 1) : R)]
   (hω : IsPrimitiveRoot ω (2 ^ (k + 1)))
   (F : biPoly R k) (G : biPoly R k) : mul_fft F G ω = mul F G := by
  unfold mul_fft
  simp only
  apply_fun fft (ω := ω)
  · simp only
    simp only [hω, fft_ifft_eq_self]
    ext i
    simp only [Vector.getElem_zipWith]
    simp only [hω, fft_eq_dft]
    unfold dft
    simp only [Vector.getElem_map]
    simp_rw [extend_eq_self]
    simp [eval_mul_eq_mul_eval]
  · intro x y p
    simp only at p
    calc
    x = ifft (fft x ω) ω := by rw [ifft_fft_eq_self]; exact hω
    _ = ifft (fft y ω) ω := by rw [p]
    _ = y                := by rw [ifft_fft_eq_self]; exact hω
