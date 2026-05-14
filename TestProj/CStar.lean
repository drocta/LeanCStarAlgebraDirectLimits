import TestProj.NormDirectLimit
import TestProj.StarDirectLimit
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.Algebra.UniformRing
import TestProj.CompletionStar
import Mathlib.Analysis.Normed.Module.Completion

section UniformContinuousStar

variable {α : Type*}

instance
    [NormedAddCommGroup α] [StarAddMonoid α] [NormedStarGroup α] :
    UniformContinuousStar α := by
  refine ⟨?_⟩
  refine Isometry.uniformContinuous ?_
  intro x y
  rw [edist_dist, edist_dist]
  rw [dist_eq_norm, dist_eq_norm, ← star_sub, norm_star]

end UniformContinuousStar


#check DirectLimit.instNorm

variable {ι : Type*} [Preorder ι] {G : ι → Type*}
variable {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {f : ∀ _ _ h, T h}
variable [∀ i j (h : i ≤ j), FunLike (T h) (G i) (G j)] [DirectedSystem G (f · · ·)]
variable [IsDirectedOrder ι]

namespace DirectLimit


#check SeminormedAddCommGroup

section NonUnitalNormedRing

variable [∀ i, NonUnitalNormedRing (G i)]
variable [∀ i j h, NonUnitalRingHomClass (T h) (G i) (G j)]
variable [NormCompat G f]

variable [Nonempty ι]

#synth ∀ i, NonUnitalRing (G i)
#check DirectLimit.instNonUnitalRingOfNonUnitalRingHomClass (G:= G)

set_option diagnostics true in
#synth NonUnitalRing (DirectLimit G f)

noncomputable instance instNonUnitalNormedRing : NonUnitalNormedRing (DirectLimit G f) where
  dist_eq := by intro x y; rfl
  norm_mul_le := by
    apply DirectLimit.induction₂ (C := fun x y => ‖x * y‖ ≤ ‖x‖ * ‖y‖)
    intro i x y
    rw [mul_def, norm_def, norm_def, norm_def]
    exact norm_mul_le x y


#check instNonUnitalNormedRing
#synth NonUnitalNormedRing (DirectLimit G f)

end NonUnitalNormedRing

section UnitalNormedRing

variable [∀ i, NormedRing (G i)]
variable [∀ i j h, RingHomClass (T h) (G i) (G j)]
variable [NormCompat G f]

variable [Nonempty ι]

noncomputable instance instNormedRing : NormedRing (DirectLimit G f) where
  dist_eq := by intro x y; rfl
  norm_mul_le := by
    apply DirectLimit.induction₂ (C := fun x y => ‖x * y‖ ≤ ‖x‖ * ‖y‖)
    intro i x y
    rw [mul_def, norm_def, norm_def, norm_def]
    exact norm_mul_le x y


#check instNormedRing
#synth NormedRing (DirectLimit G f)

end UnitalNormedRing

section CStarRing

variable [∀ i, NonUnitalNormedRing (G i)] [∀ i, StarRing (G i)] [∀ i, CStarRing (G i)]
variable [∀ i j h, StarHomClass (T h) (G i) (G j)]
variable [∀ i j h, NonUnitalRingHomClass (T h) (G i) (G j)]
variable [NormCompat G f]
variable [Nonempty ι]


instance instCStarRing :
    CStarRing (DirectLimit G f) where
  norm_mul_self_le := by
    apply DirectLimit.induction (C := fun x => ‖x‖ * ‖x‖ ≤ ‖star x * x‖)
    intro i x
    rw [star_def, mul_def, norm_def, norm_def]
    apply CStarRing.norm_mul_self_le

end CStarRing

section CompletionCStarRing
/- Because  Mathlib.Topology.Algebra.UniformRing currently only supports completion for
*unital* rings, we are for the moment considering only unital `CStarRing`s-/

variable [∀ i, NormedRing (G i)] [∀ i, StarRing (G i)] [∀ i, CStarRing (G i)]
variable [∀ i j h, StarHomClass (T h) (G i) (G j)]
variable [∀ i j h, RingHomClass (T h) (G i) (G j)]
variable [NormCompat G f]

variable [Nonempty ι]

noncomputable local instance (priority := high) : TopologicalSpace (DirectLimit G f) :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace





example : @IsTopologicalRing (DirectLimit G f)
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace _  := by
  infer_instance




open UniformSpace

--todo : should not have this section be named "boogie", either rename it or make it not a section
section boogie

variable {α : Type*} [NormedRing α] [StarRing α] [CStarRing α]

instance : CStarRing (Completion α) where
  norm_mul_self_le := by
    intro x
    apply Completion.induction_on (p := fun x => ‖x‖ * ‖x‖ ≤ ‖star x * x‖)
    · -- show the set {x | ‖x‖ * ‖x‖ ≤ ‖star x * x‖} is closed
      refine isClosed_le ?_ ?_
      · -- show Continuous (fun x : Completion α => ‖x‖ * ‖x‖)
        fun_prop
      · -- show Continuous (fun a : Completion α => ‖star a * a‖)
        fun_prop
    · -- show that for each a : α, we have ‖↑a‖ * ‖↑a‖ ≤ ‖star (↑a) * ↑a‖
      intro a
      --todo: the `_root_.star_def` is to get the one from the completion, rather than the direct limit
      -- but it shouldn't be in the root namespace, so CompletionStar.lean should put it in a namespace.
      rw [_root_.star_def, ← Completion.coe_mul, Completion.norm_coe, Completion.norm_coe]
      apply CStarRing.norm_mul_self_le

#synth CStarRing (Completion α)
end boogie

end CompletionCStarRing


section CStarAlgebra

variable [∀ i, CStarAlgebra (G i)]
#synth ∀ i, NormedRing (G i)
#synth ∀ i, StarRing (G i)
#synth ∀ i, CStarRing (G i)
variable [∀ i j h, StarHomClass (T h) (G i) (G j)]
variable [∀ i j h, AlgHomClass (T h) ℂ (G i) (G j)]
#synth ∀ i j h, RingHomClass (T h) (G i) (G j)
variable [NormCompat G f]

variable [Nonempty ι]

open UniformSpace
#synth CStarRing (Completion (DirectLimit G f))
#synth ∀ i, Algebra ℂ (G i)
--variable [∀ i j h, AlgHomClass (T h) ℂ (G i) (G j)]
#synth Algebra ℂ (DirectLimit G f)

local instance {A : Type*} [UniformSpace A] [Ring A] [Algebra ℂ A]
    [IsUniformAddGroup A] [IsTopologicalRing A] : UniformContinuousConstSMul ℂ A :=
  uniformContinuousConstSMul_of_continuousConstSMul ℂ A


instance : NormSMulClass ℂ (DirectLimit G f) where
  norm_smul := by
    intro r x
    apply DirectLimit.induction (C := fun x => ‖r • x‖ = ‖r‖ * ‖x‖)
    intro i x
    rw [smul_def, norm_def, norm_def]
    apply norm_smul

noncomputable instance : CStarAlgebra (Completion (DirectLimit G f)) where
  norm_smul_le := by
    intro r x
    apply Completion.induction_on (p := fun x => ‖r • x‖ ≤ ‖r‖ * ‖x‖) x
    · -- show the set {a | ‖r • a‖ ≤ ‖r‖ * ‖a‖} is closed
      refine isClosed_le ?_ ?_
      · -- show Continuous (fun x : Completion (DirectLimit G f) => ‖r • x‖)
        refine continuous_norm.comp ?_
        apply Completion.continuous_map
      · -- show Continuous (fun x : Completion (DirectLimit G f) => ‖r‖ * ‖x‖)
        apply (continuous_const.mul continuous_norm)
    · -- show that for each a : DirectLimit G f, we have ‖r • ↑a‖ ≤ ‖r‖ * ‖↑a‖
      intro a
      rw [Completion.smul_def]
      have h : UniformContinuous fun (x : DirectLimit G f) ↦ r • x := by
        apply uniformContinuous_const_smul
      rw [Completion.map_coe h, @Completion.norm_coe, @Completion.norm_coe]
      apply norm_smul_le
  star_smul := by
    intro r x
    apply Completion.induction_on (p := fun x => star (r • x) = star r • star x) x
    · -- show the set {a | star (r • a) = star r • star a} is closed
      refine isClosed_eq ?_ ?_
      · -- show ⊢ Continuous fun a ↦ star (r • a)
        refine continuous_star.comp ?_
        apply Completion.continuous_map
      · -- show ⊢ Continuous fun a ↦ star r • star a
        refine (continuous_const.smul continuous_star).comp continuous_id
    · -- show that for each a : DirectLimit G f, we have star (r • ↑a) = star r • star (↑a)
      intro a
      --todo: the `_root_.star_def` is to get the one from the completion, rather than the direct limit
      -- but it shouldn't be in the root namespace, so CompletionStar.lean should put it in a namespace.
      rw [Completion.smul_def, _root_.star_def, Completion.smul_def]
      rw [Completion.map_coe (uniformContinuous_const_smul r), Completion.map_coe (uniformContinuous_const_smul (star r))]
      -- TODO : again, the `_root_.star_def` is to get the one from the completion, but it shouldn't be in the root namespace
      rw [_root_.star_def, @star_smul]

section someCasts

variable (A B R : Type*) [Semiring A] [Semiring B] [CommSemiring R] [Star A] [Star B]
variable [Algebra R A] [Algebra R B]

#check A
def _root_.NonUnitalStarAlgHom.toStarRingHom (f : A →⋆ₙₐ[R] B) : A →⋆ₙ+* B where
  toFun := f
  map_zero' := f.map_zero'
  map_add' := f.map_add'
  map_mul' := f.map_mul'
  map_star' := f.map_star'

end someCasts

namespace CStarAlgebra

#synth CStarAlgebra (Completion (DirectLimit G f))

variable (A : Type*) [CStarAlgebra A]
def lift (g : ∀ i, G i →⋆ₐ[ℂ] A) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x) :
    DirectLimit G f →⋆ₐ[ℂ] A where
  __ := DirectLimit.Ring.lift (G := G) (f := f) (P := A) (g := fun i => (g i).toAlgHom) (Hg := Hg)
  __ := DirectLimit.StarRing.lift (G := G) (f := f) (A := A) (g := fun i => (g i).toNonUnitalStarAlgHom.toStarRingHom) (Hg := Hg)
  toFun := _root_.DirectLimit.lift _ (g · ·) fun i j h x ↦ (Hg i j h x).symm

end CStarAlgebra


end CStarAlgebra

end DirectLimit
