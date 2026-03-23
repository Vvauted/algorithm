import Mathlib.Data.Nat.Log
import Mathlib.Data.Vector.Basic
import Mathlib.Tactic
import Algorithm.Poly.cPoly

abbrev biPoly (R : Type _) (k : Nat) := Vector R (2 ^ k)
variable {R : Type _} [AddCommMonoid R] [Mul R] [Pow R ℕ]

namespace biPoly
def eval (f : biPoly R k) (x : R) : R :=
  ∑ i : Fin (2 ^ k), f[i] * x ^ i.val

def even (f : biPoly R (k + 1)) : biPoly R k :=
  Vector.ofFn fun i => f[2 * i.val]

def odd (f : biPoly R (k + 1)) : biPoly R k :=
  Vector.ofFn fun i => f[2 * i.val + 1]

def spilt_L (f : biPoly R (k + 1)) : biPoly R k :=
  Vector.ofFn fun i => f[i]

def extend (f : biPoly R k) : biPoly R (k + 1) :=
  (f.rightpad (2 ^ (k + 1)) 0).cast (by simp [pow_succ])

def mul (F : biPoly R k) (G : biPoly R k) : biPoly R (k + 1) :=
  Vector.ofFn fun i =>
    ∑ j : Fin (2 ^ k), ∑ k : Fin (2 ^ k), if j.val + k.val = i then F[j] * G[k] else 0

def tocPoly (F : biPoly R k) : cPoly R := F.toArray

instance {R : Type _} {k : Nat} : CoeOut (biPoly R k) (cPoly R) := ⟨biPoly.tocPoly⟩

end biPoly

omit [Mul R] [Pow R ℕ] in
@[simp]
lemma getElem_extend (f : biPoly R k) {i : ℕ} (hi) :
  f.extend[i]'hi = if w : i < 2 ^ k then f[i] else 0 := by
  unfold biPoly.extend
  simp only [Vector.rightpad, Vector.cast_cast, Vector.getElem_cast]
  split_ifs with h
  · erw [Vector.getElem_append_left]
  · erw [Vector.getElem_append_right]
    · simp only [Vector.getElem_replicate]
    · omega

namespace cPoly

def tobiPoly_size (F : cPoly R) : Nat :=
  if F.size = 0 then 0 else (Nat.log2 (F.size - 1) + 1)

omit [Mul R] [Pow R ℕ] [AddCommMonoid R] in
theorem self_size_le_tobiPoly_size (F : cPoly R) :
  F.size ≤ 2 ^ F.tobiPoly_size := by
  unfold tobiPoly_size
  simp only [Array.size_eq_zero_iff, pow_ite]
  split_ifs with p
  · simp [p]
  · have p := Nat.lt_log2_self (n := F.size - 1)
    omega

def tobiPoly (F : cPoly R) : biPoly R (tobiPoly_size F) :=
  (F.toVector.rightpad (2 ^ (tobiPoly_size F)) 0).cast (by simp [self_size_le_tobiPoly_size])

end cPoly
