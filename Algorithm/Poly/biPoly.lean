import Mathlib
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

def tobiPoly (F : cPoly) : biPoly :=


end cPoly
