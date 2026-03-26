import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Algebra.Star.Basic

namespace DirectLimit

variable {ι : Type*} [Preorder ι] {G : ι → Type*}
variable {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {f : ∀ _ _ h, T h}
variable [∀ i j (h : i ≤ j), FunLike (T h) (G i) (G j)] [DirectedSystem G (f · · ·)]
variable [IsDirectedOrder ι]

section Star
variable [∀ i, Star (G i)] [∀ i j h, StarHomClass (T h) (G i) (G j)]
instance : Star (DirectLimit G f) where
  star := DirectLimit.map f f (fun _ x => star x) (compat := by
    intro i j h
    exact StarHomClass.map_star (f i j h)
  )



lemma star_def (i : ι) (x : G i) :
    star ⟦⟨i, x⟩⟧ = (⟦⟨i, star x ⟩⟧ : DirectLimit G f) := by
  rfl



end Star

section InvolutiveStar
variable [∀ i, InvolutiveStar (G i)] [∀ i j h, StarHomClass (T h) (G i) (G j)]
instance : InvolutiveStar (DirectLimit G f) where
  star_involutive := by
    apply DirectLimit.induction
    intro i x
    rw [star_def, star_def, star_star]

end InvolutiveStar

private lemma of_eq_of_le (i k : ι) (hik : i ≤ k) (x : G i) :
    (⟦⟨i, x⟩⟧ : DirectLimit G f) = ⟦⟨k, (f i k hik) x⟩⟧ :=
  eq_of_le (f := f) ⟨i, x⟩ k hik

section StarMul
variable [∀ i, Mul (G i)] [∀ i j h, MulHomClass (T h) (G i) (G j)]
variable [∀ i, StarMul (G i)] [∀ i j h, StarHomClass (T h) (G i) (G j)]

instance : StarMul (DirectLimit G f) where
  star_mul := by
    intro r s
    induction r using DirectLimit.induction with
    | ih i x => induction s using DirectLimit.induction with
      | ih j y =>
        obtain ⟨k, hik, hjk⟩ := directed_of (α := ι) (· ≤ ·) i j
        have star_r_eq_star_r' := of_eq_of_le (f := f) i k hik (star x)
        have star_s_eq_star_s' := of_eq_of_le (f := f) j k hjk (star y)
        have r_eq_r' := of_eq_of_le (f := f) i k hik x
        have s_eq_s' := of_eq_of_le (f := f) j k hjk y
        rw [star_def, star_def]
        rw [star_r_eq_star_r', star_s_eq_star_s', s_eq_s', r_eq_r']
        rw [mul_def, mul_def, map_star, map_star]
        rw [← star_mul, ← star_def]



end StarMul

section StarAddMonoid

variable [∀ i, AddMonoid (G i)] [∀ i j h, AddMonoidHomClass (T h) (G i) (G j)]
variable [∀ i, StarAddMonoid (G i)] [∀ i j h, StarHomClass (T h) (G i) (G j)]

/- we need [Nonempty ι] in order to be able to synthesize an instance of AddMonoid
using DirectLimit.instAddMonoid-/
variable [Nonempty ι]

instance : StarAddMonoid (DirectLimit G f) where
  star_add := by
    intro r s
    induction r using DirectLimit.induction with
    | ih i x => induction s using DirectLimit.induction with
      | ih j y =>
        obtain ⟨k, hik, hjk⟩ := directed_of (α := ι) (· ≤ ·) i j
        have star_r_eq_star_r' := of_eq_of_le (f := f) i k hik (star x)
        have star_s_eq_star_s' := of_eq_of_le (f := f) j k hjk (star y)
        have r_eq_r' := of_eq_of_le (f := f) i k hik x
        have s_eq_s' := of_eq_of_le (f := f) j k hjk y
        rw [star_def, star_def]
        rw [star_r_eq_star_r', star_s_eq_star_s', s_eq_s', r_eq_r']
        rw [add_def, add_def, map_star, map_star]
        rw [← star_add, ← star_def]

end StarAddMonoid

section StarRing

variable [∀ i, NonUnitalNonAssocSemiring (G i)] [∀ i j h, NonUnitalRingHomClass (T h) (G i) (G j)]
variable [∀ i, StarRing (G i)] [∀ i j h, StarHomClass (T h) (G i) (G j)]
variable [Nonempty ι]
instance : StarRing (DirectLimit G f) where
  star_mul := by
    intro r s
    induction r using DirectLimit.induction with
    | ih i x => induction s using DirectLimit.induction with
      | ih j y =>
        obtain ⟨k, hik, hjk⟩ := directed_of (α := ι) (· ≤ ·) i j
        have star_r_eq_star_r' := of_eq_of_le (f := f) i k hik (star x)
        have star_s_eq_star_s' := of_eq_of_le (f := f) j k hjk (star y)
        have r_eq_r' := of_eq_of_le (f := f) i k hik x
        have s_eq_s' := of_eq_of_le (f := f) j k hjk y
        rw [star_def, star_def]
        rw [star_r_eq_star_r', star_s_eq_star_s', s_eq_s', r_eq_r']
        rw [mul_def, mul_def, map_star, map_star]
        rw [← star_mul, ← star_def]
  star_add := by
    intro r s
    induction r using DirectLimit.induction with
    | ih i x => induction s using DirectLimit.induction with
      | ih j y =>
        obtain ⟨k, hik, hjk⟩ := directed_of (α := ι) (· ≤ ·) i j
        have star_r_eq_star_r' := of_eq_of_le (f := f) i k hik (star x)
        have star_s_eq_star_s' := of_eq_of_le (f := f) j k hjk (star y)
        have r_eq_r' := of_eq_of_le (f := f) i k hik x
        have s_eq_s' := of_eq_of_le (f := f) j k hjk y
        rw [star_def, star_def]
        rw [star_r_eq_star_r', star_s_eq_star_s', s_eq_s', r_eq_r']
        rw [add_def, add_def, map_star, map_star]
        rw [← star_add, ← star_def]
end StarRing

section StarModule

variable {R : Type*} [Semiring R] [Star R]
variable [∀ i, Star (G i)] [∀ i j h, StarHomClass (T h) (G i) (G j)]
variable [∀ i, SMul R (G i)] [∀ i j h, MulActionHomClass (T h) R (G i) (G j)]
variable [∀ i, AddZero (G i)]
variable [∀ i, StarModule R (G i)] [∀ i j h, AddMonoidHomClass (T h) (G i) (G j)]

instance : StarModule R (DirectLimit G f) where
  star_smul := by
    intro r
    apply DirectLimit.induction
    intro i x
    rw [star_def, smul_def, smul_def, ← star_smul, star_def]

end StarModule


end DirectLimit
