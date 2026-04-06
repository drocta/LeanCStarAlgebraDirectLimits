import TestProj.NormDirectLimit
import TestProj.StarDirectLimit
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Topology.Algebra.UniformRing
import TestProj.CompletionStar

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

section CompletionOfNormedRing

/- turns out this section is entirely unnecessary because the completion of a normed ring
is already a normed ring by the instance provided in Mathlib.Analysis.Normed.Module.Completion.lean.
I didn't know this.
I am keeping this here for this one commit, and will delete it in the next commit.
-/
variable (α : Type*) [NormedRing α]

open UniformSpace

#check Completion α
#synth Ring (Completion α)
#synth Norm (Completion α)

noncomputable instance : Norm (Completion α) where
  norm := Completion.extension (fun (a: α) ↦ norm a)

lemma norm_def (a : α) : ‖(↑a : Completion α)‖ = ‖a‖ :=
  Completion.extension_coe (f := fun a : α ↦ norm a) uniformContinuous_norm a

#synth Norm (Completion α)

#synth NonUnitalNormedRing (Completion α)

#synth MetricSpace (Completion α)
#synth MetricSpace α

#check sub_self
#synth AddGroup (Completion α)

example : Continuous (fun x : Completion α => norm (x - x)) := by
  have h1 : ∀ x : Completion α, norm (x - x) = norm (0 : Completion α) := by intro x; rw [sub_self]
  have h2 : Continuous (fun x : Completion α => norm (0 : Completion α)) := continuous_const
  have h3 : (fun x : Completion α => norm (x - x)) =
    (fun x : Completion α => norm (0 : Completion α)) :=
    by ext x; rw [h1 x]
  rw [h3]
  exact h2

example : Continuous (fun x : Completion α => norm (x - x)) := by
  simpa using (continuous_const : Continuous fun _ : Completion α => norm (0 : Completion α))

example : ∀ x : α ,  norm (↑ x : Completion α) = norm x := by
  exact Completion.extension_coe (f := fun a : α ↦ norm a) uniformContinuous_norm

example : UniformContinuous (fun x : Completion α => norm x) := by
  apply Completion.uniformContinuous_extension

example : Continuous (fun x : Completion α => norm x) := by
  apply Completion.continuous_extension

example : Continuous (fun p : Completion α × Completion α => norm (p.1 - p.2)) := by
  have h1 := continuous_sub (G := Completion α)
  have h2 := Completion.continuous_extension (α := α) (f := fun a : α ↦ norm a)
  have h3 : Continuous (fun p : Completion α × Completion α => norm (p.1 - p.2))
    := h2.comp h1
  exact h3

example : Continuous (fun p : Completion α × Completion α => norm (p.1 - p.2)) := by
  --have h1 := continuous_sub (G := Completion α)
  have h := Completion.continuous_extension (α := α) (f := fun a : α ↦ norm a)
  exact h.comp (continuous_sub (G := Completion α))

example : Continuous (fun p : Completion α × Completion α => norm (p.1 - p.2)) := by
  exact (Completion.continuous_extension (α := α) (f := fun a : α ↦ norm a)).comp
    (continuous_sub (G := Completion α))

example : Continuous (fun p : Completion α × Completion α => norm (p.1 - p.2)) := by
  simpa using (continuous_norm (E := Completion α)).comp (continuous_sub (G := Completion α))


lemma continuous_diagonal {X : Type*} [NormedRing X] : Continuous (fun x : X => (x, x)) := by
  exact Continuous.prodMk continuous_id continuous_id


example :
    IsClosed {x : Completion α × Completion α × Completion α |
      ‖x.1 - x.2.2‖ ≤ ‖x.1 - x.2.1‖ + ‖x.2.1 - x.2.2‖} := by
  have hnorm : Continuous (fun x : Completion α => ‖x‖) :=
    Completion.continuous_extension (α := α) (f := fun a : α => ‖a‖)
  have hxz : Continuous (fun x : Completion α × Completion α × Completion α =>
      x.1 - x.2.2) := by
    fun_prop
  have hxy : Continuous (fun x : Completion α × Completion α × Completion α =>
      x.1 - x.2.1) := by
    fun_prop
  have hyz : Continuous (fun x : Completion α × Completion α × Completion α =>
      x.2.1 - x.2.2) := by
    fun_prop
  refine isClosed_le (hnorm.comp hxz) ((hnorm.comp hxy).add (hnorm.comp hyz))



noncomputable instance : MetricSpace (Completion α) where
  dist := fun x y => ‖x - y‖
  dist_self := by
    intro x
    apply Completion.induction_on (α := α) (p := fun x => ‖x - x‖ = 0)
    · -- show the set {x | ‖x - x‖ = 0} is closed
      have h1 : Continuous (fun x : Completion α => norm (x - x)) := by
        simpa using (continuous_const : Continuous fun _ : Completion α => norm (0 : Completion α))
      exact isClosed_eq
        h1 --TODO: consider inlining this h1?
        continuous_const
    · -- show that for each a : α, we have ‖↑a - ↑a‖ = 0
      intro a
      rw [sub_self, ← Completion.coe_zero, norm_def, norm_zero]
  dist_comm := by
    intro x y
    apply Completion.induction_on₂ (α := α) (β := α) (p := fun x y => ‖x - y‖ = ‖y - x‖)
    · -- show the set {x | ‖x - y‖ = ‖y - x‖} is closed
      have h1 : Continuous (fun p : Completion α × Completion α => norm (p.1 - p.2)) := by
        exact (Completion.continuous_extension (α := α) (f := fun a : α ↦ norm a)).comp
          (continuous_sub (G := Completion α))
      have h2 : Continuous (fun p : Completion α × Completion α => norm (p.2 - p.1)) :=
        h1.comp continuous_swap
      exact isClosed_eq
        h1
        h2
    · -- show that for each a b : α, we have ‖↑a - ↑b‖ = ‖↑b - ↑a‖
      intro a b
      simp only [← Completion.coe_sub, norm_def]
      rw [← norm_neg, neg_sub]
  dist_triangle := by
    intro x y z
    have norm_continuous := (Completion.continuous_extension (α := α) (f := fun a : α ↦ norm a))
    apply Completion.induction_on₃ (α := α) (β := α) (γ := α) (p := fun x y z => ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖)
    · -- goal : IsClosed {x | ‖x.1 - x.2.2‖ ≤ ‖x.1 - x.2.1‖ + ‖x.2.1 - x.2.2‖}
      /-
      have hxz : Continuous (fun x : Completion α × Completion α × Completion α => norm (x.1 - x.2.2)) := by
        apply norm_continuous.comp
        exact continuous_sub.comp
          (Continuous.prodMk continuous_fst (continuous_snd.comp continuous_snd))
      -/
      have hxz' : Continuous (fun x : Completion α × Completion α × Completion α =>
        x.1 - x.2.2) := by
        fun_prop
      have hxy' : Continuous (fun x : Completion α × Completion α × Completion α =>
        x.1 - x.2.1) := by
        fun_prop
      have hyz' : Continuous (fun x : Completion α × Completion α × Completion α =>
        x.2.1 - x.2.2) := by
        fun_prop
      exact isClosed_le (norm_continuous.comp hxz') ((norm_continuous.comp hxy').add (norm_continuous.comp hyz'))
      /-
            have hxy' : Continuous
      have hxy : Continuous (fun x : Completion α × Completion α × Completion α => norm (x.1 - x.2.1)) := by
        apply norm_continuous.comp
        fun_prop
        --exact continuous_sub.comp
        --  (Continuous.prodMk continuous_fst (continuous_fst.comp continuous_snd))
      have hyz : Continuous (fun x : Completion α × Completion α × Completion α => norm (x.2.1 - x.2.2)) := by
        apply norm_continuous.comp
        fun_prop
        -- exact continuous_sub.comp continuous_snd
      have h_xy_p_yz : Continuous (fun x : Completion α × Completion α × Completion α =>
        norm (x.1 - x.2.1) + norm (x.2.1 - x.2.2)) := by
        exact (continuous_add.comp (Continuous.prodMk hxy hyz))
      refine isClosed_le ?_ ?_
      · -- show that the function x ↦ ‖x.1 - x.2.2‖ is continuous
        apply norm_continuous.comp
        fun_prop
      · -- show that the function x ↦ ‖x.1 - x.2.1‖ + ‖x.2.1 - x.2.2‖ is continuous
        exact h_xy_p_yz --sorry-- apply continuous_add.comp

      -/

      --exact isClosed_le hxz h_xy_p_yz
    · -- show that for each a b c : α, we have ‖↑a - ↑c‖ ≤ ‖↑a - ↑b‖ + ‖↑b - ↑c‖
      intro a b c
      simp only [← Completion.coe_sub, norm_def]
      rw [← NormedAddGroup.dist_eq, ← NormedAddGroup.dist_eq, ← NormedAddGroup.dist_eq]
      exact dist_triangle a b c
  eq_of_dist_eq_zero := by
    sorry
    --rw [← Completion.coe_sub, norm_def, norm_comm]
--noncomputable instance : NormedRing (Completion α) where

end CompletionOfNormedRing


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
--variable (hnorm : ∀ i j h x, ‖(x : G i)‖ = ‖((f i j h) x : G j)‖)
variable [NormCompat G f]

variable [Nonempty ι]

#synth ∀ i, NonUnitalRing (G i)
#check DirectLimit.instNonUnitalRingOfNonUnitalRingHomClass (G:= G)

set_option diagnostics true in
#synth NonUnitalRing (DirectLimit G f)

noncomputable instance instNonUnitalNormedRing : NonUnitalNormedRing (DirectLimit G f) := by
  --letI := DirectLimit.instNorm hnorm
  --letI := DirectLimit.instNormedAddCommGroup hnorm
  exact {
    dist_eq := by intro x y; rfl
    norm_mul_le := by
      apply DirectLimit.induction₂ (C := fun x y => ‖x * y‖ ≤ ‖x‖ * ‖y‖)
      intro i x y
      rw [mul_def, norm_def, norm_def, norm_def]
      exact norm_mul_le x y
  }

#check instNonUnitalNormedRing
#synth NonUnitalNormedRing (DirectLimit G f)

end NonUnitalNormedRing

section UnitalNormedRing

variable [∀ i, NormedRing (G i)]
variable [∀ i j h, RingHomClass (T h) (G i) (G j)]
--variable (hnorm : ∀ i j h x, ‖(x : G i)‖ = ‖((f i j h) x : G j)‖)
variable [NormCompat G f]

variable [Nonempty ι]

noncomputable instance instNormedRing : NormedRing (DirectLimit G f) := by
  exact {
    dist_eq := by intro x y; rfl
    norm_mul_le := by
      apply DirectLimit.induction₂ (C := fun x y => ‖x * y‖ ≤ ‖x‖ * ‖y‖)
      intro i x y
      rw [mul_def, norm_def, norm_def, norm_def]
      exact norm_mul_le x y
  }

#check instNormedRing
#synth NormedRing (DirectLimit G f)

end UnitalNormedRing

section CStarRing

variable [∀ i, NonUnitalNormedRing (G i)] [∀ i, StarRing (G i)] [∀ i, CStarRing (G i)]
variable [∀ i j h, StarHomClass (T h) (G i) (G j)]
variable [∀ i j h, NonUnitalRingHomClass (T h) (G i) (G j)]
--variable (hnorm : ∀ i j h x, ‖(x : G i)‖ = ‖((f i j h) x : G j)‖)
variable [NormCompat G f]

variable [Nonempty ι]



#synth Star (DirectLimit G f)
#synth NonUnitalNonAssocSemiring (DirectLimit G f)
#synth StarRing (DirectLimit G f)
#synth NonUnitalNormedRing (DirectLimit G f)


instance instCStarRing :
    --letI : NonUnitalNormedRing (DirectLimit G f) := instNonUnitalNormedRing hnorm
    CStarRing (DirectLimit G f) := by
  --letI : NonUnitalNormedRing (DirectLimit G f) := instNonUnitalNormedRing hnorm
  exact {
    norm_mul_self_le := by
      apply DirectLimit.induction (C := fun x => ‖x‖ * ‖x‖ ≤ ‖star x * x‖)
      intro i x
      rw [star_def, mul_def, norm_def, norm_def]
      apply CStarRing.norm_mul_self_le
  }

#check instCStarRing
#synth CStarRing (DirectLimit G f)

end CStarRing

section Test

--variable [NormedRing (DirectLimit G f)]
variable [∀ i, NormedRing (G i)] [∀ i, StarRing (G i)] [∀ i, CStarRing (G i)]
variable [∀ i j h, StarHomClass (T h) (G i) (G j)]
variable [∀ i j h, RingHomClass (T h) (G i) (G j)]
variable [NormCompat G f]
variable [Nonempty ι]
/-
#synth UniformSpace (DirectLimit G f)
#synth TopologicalSpace (DirectLimit G f)
#synth IsTopologicalRing (DirectLimit G f)
#synth NonUnitalSeminormedRing (DirectLimit G f)

#check NonUnitalNormedRing.toNonUnitalSeminormedRing
#check UniformSpace.toTopologicalSpace
-/


set_option diagnostics true in
set_option trace.Meta.synthInstance true in
example : @IsTopologicalRing (DirectLimit G f)
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace _ := by
  infer_instance
  --letI i1 := @NonUnitalSeminormedRing.toIsTopologicalRing (α := DirectLimit G f) _
  --exact i1
  --letI : UniformSpace (DirectLimit G f) := by infer_instance
  --letI : TopologicalSpace (DirectLimit G f) := UniformSpace.toTopologicalSpace
  --apply NonUnitalSeminormedRing.toIsTopologicalRing (α := DirectLimit G f)
  --apply NonUnitalNormedRing.toNonUnitalSeminormedRing
  --infer_instance

end Test

/-
noncomputable section StarCompletion

open UniformSpace

variable {α : Type*} [UniformSpace α]

instance [Star α] : Star (UniformSpace.Completion α) :=
  ⟨Completion.map (fun a ↦ star a : α → α)⟩

instance [Mul α] [StarMul α] [Mul (UniformSpace.Completion α)] : StarMul (UniformSpace.Completion α) where
  star_mul := by
    apply Completion.map₂ (fun a b ↦ star (a * b) : α → α → α)
    intro a₁ a₂ b₁ b₂
    rw [star_mul, star_mul]

end StarCompletion
-/



section CompletionCStarRing
/- Because  Mathlib.Topology.Algebra.UniformRing currently only supports completion for
*unital* rings, we are for the moment considering only unital `CStarRing`s-/

variable [∀ i, NormedRing (G i)] [∀ i, StarRing (G i)] [∀ i, CStarRing (G i)]
variable [∀ i j h, StarHomClass (T h) (G i) (G j)]
variable [∀ i j h, RingHomClass (T h) (G i) (G j)]
--variable (hnorm : ∀ i j h x, ‖(x : G i)‖ = ‖((f i j h) x : G j)‖)
variable [NormCompat G f]

variable [Nonempty ι]

noncomputable local instance (priority := high) : TopologicalSpace (DirectLimit G f) :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace


#synth ∀ i, IsTopologicalRing (G i)
#synth IsTopologicalRing (DirectLimit G f)
#synth NormedRing (DirectLimit G f)
#synth UniformSpace (DirectLimit G f)
#synth @IsTopologicalRing (DirectLimit G f)
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace _


example : @IsTopologicalRing (DirectLimit G f)
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace _  := by
  infer_instance

section alpha

variable (α : Type*) [NormedRing α] --[UniformSpace α]
#synth IsTopologicalRing α
#synth Ring (UniformSpace.Completion α )
#synth NonUnitalNormedRing (UniformSpace.Completion α)
#synth UniformSpace α

end alpha

#check instCStarRing (G := G) (f := f)

#check (letI : NonUnitalNormedRing (DirectLimit G f) := instNonUnitalNormedRing
       @PseudoMetricSpace.toUniformSpace (DirectLimit G f) inferInstance)

--letI : NonUnitalNormedRing (DirectLimit G f) := instNonUnitalNormedRing hnorm
--#check @PseudoMetricSpace.toUniformSpace (DirectLimit G f) ((instNonUnitalNormedRing hnorm))

instance foo {X : Type*} (h : NonUnitalNormedRing X) : UniformSpace X :=
  h.toNonUnitalSeminormedRing.toPseudoMetricSpace.toUniformSpace

instance foo2 {X : Type*} (h : NormedRing X) : UniformSpace X :=
  h.toSeminormedRing.toPseudoMetricSpace.toUniformSpace

#check foo (instNonUnitalNormedRing )

#check @UniformSpace.Completion _ (foo (instNonUnitalNormedRing ))

#synth Ring (@UniformSpace.Completion _ (foo (instNonUnitalNormedRing (G := G) (f := f)) ))




def bar :=
  --letI : NonUnitalNormedRing (DirectLimit G f) := instNonUnitalNormedRing
  UniformSpace.Completion (DirectLimit G f)

variable (G f) in
abbrev bar2 :=
  --letI : NormedRing (DirectLimit G f) := instNormedRing
  UniformSpace.Completion (DirectLimit G f)

#check bar

example : (@UniformSpace.Completion _ (foo2 (instNormedRing (G := G) (f := f) ))) =
    (bar2 (G := G) (f := f) ) := rfl
#synth Ring (@UniformSpace.Completion _ (foo2 (instNormedRing (G := G) (f := f))))

--set_option diagnostics true in
#synth Mul (bar2 (G := G) (f := f))

--variable [NonUnitalNormedRing (DirectLimit G f)]
#synth PseudoMetricSpace (DirectLimit G f)


#check (UniformSpace.Completion (DirectLimit G f))


open UniformSpace

#synth ∀ i, ContinuousStar (G i)
#synth NormedStarGroup (DirectLimit G f)
#synth ContinuousStar (DirectLimit G f)
#synth UniformSpace (DirectLimit G f)
#synth NormedRing (DirectLimit G f)
#synth Star (Completion (DirectLimit G f))
#synth StarMul (Completion (DirectLimit G f))

#synth StarRing (Completion (DirectLimit G f))
#synth NormedRing (Completion (DirectLimit G f))
#synth NormedRing (DirectLimit G f)

#synth @ContinuousStar (DirectLimit G f) PseudoMetricSpace.toUniformSpace.toTopologicalSpace _

/-
instance instContinuousStar : @ContinuousStar (DirectLimit G f)
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace _ := by
  exact NormedStarGroup.to_continuousStar (E := DirectLimit G f)
#check instContinuousStar
#synth ContinuousStar (DirectLimit G f)
#synth @ContinuousStar (DirectLimit G f) PseudoMetricSpace.toUniformSpace.toTopologicalSpace _
-/

--instance : Star (Completion (DirectLimit G f)) where
--  star :=





end CompletionCStarRing

end DirectLimit
