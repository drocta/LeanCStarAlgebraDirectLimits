import TestProj.NormDirectLimit
import TestProj.StarDirectLimit
import Mathlib.Analysis.CStarAlgebra.Basic


#check DirectLimit.instNorm

variable {ι : Type*} [Preorder ι] {G : ι → Type*}
variable {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {f : ∀ _ _ h, T h}
variable [∀ i j (h : i ≤ j), FunLike (T h) (G i) (G j)] [DirectedSystem G (f · · ·)]
variable [IsDirectedOrder ι]

namespace DirectLimit

section SeminormedAddCommGroup

end SeminormedAddCommGroup

#check SeminormedAddCommGroup

section NonUnitalNormedRing

variable [∀ i, NonUnitalNormedRing (G i)]
variable [∀ i j h, NonUnitalRingHomClass (T h) (G i) (G j)]
variable (hnorm : ∀ i j h x, ‖(x : G i)‖ = ‖((f i j h) x : G j)‖)

variable [Nonempty ι]

#synth ∀ i, NonUnitalRing (G i)
#check DirectLimit.instNonUnitalRingOfNonUnitalRingHomClass (G:= G)

set_option diagnostics true in
#synth NonUnitalRing (DirectLimit G f)

noncomputable instance instNonUnitalNormedRing : NonUnitalNormedRing (DirectLimit G f) := by
  letI := DirectLimit.instNorm hnorm
  letI := DirectLimit.instNormedAddCommGroupOfNormedAddCommGroup hnorm
  exact {
    dist_eq := by intro x y; rfl
    norm_mul_le := by
      apply DirectLimit.induction₂ (C := fun x y => ‖x * y‖ ≤ ‖x‖ * ‖y‖)
      intro i x y
      rw [mul_def, norm_def, norm_def, norm_def]
      exact norm_mul_le x y
  }

#check instNonUnitalNormedRing

end NonUnitalNormedRing


section CStarRing

variable [∀ i, NonUnitalNormedRing (G i)] [∀ i, StarRing (G i)] [∀ i, CStarRing (G i)]
variable [∀ i j h, StarHomClass (T h) (G i) (G j)]
variable [∀ i j h, NonUnitalRingHomClass (T h) (G i) (G j)]
variable (hnorm : ∀ i j h x, ‖(x : G i)‖ = ‖((f i j h) x : G j)‖)

variable [Nonempty ι]



#synth Star (DirectLimit G f)
#synth NonUnitalNonAssocSemiring (DirectLimit G f)
#synth StarRing (DirectLimit G f)
--#synth NonUnitalNormedRing (DirectLimit G f)


instance instCStarRing (hnorm) :
    letI : NonUnitalNormedRing (DirectLimit G f) := instNonUnitalNormedRing hnorm
    CStarRing (DirectLimit G f) := by
  letI : NonUnitalNormedRing (DirectLimit G f) := instNonUnitalNormedRing hnorm
  exact {
    norm_mul_self_le := by
      apply DirectLimit.induction (C := fun x => ‖x‖ * ‖x‖ ≤ ‖star x * x‖)
      intro i x
      rw [star_def, mul_def, norm_def, norm_def]
      apply CStarRing.norm_mul_self_le
  }

#check instCStarRing hnorm

end CStarRing

end DirectLimit
