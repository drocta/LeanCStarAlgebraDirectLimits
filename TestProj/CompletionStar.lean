import Mathlib.Topology.Algebra.Star
import Mathlib.Topology.Algebra.GroupCompletion
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Topology.Constructions.SumProd


noncomputable section

open UniformSpace

class UniformContinuousStar (α : Type*) [UniformSpace α] [Star α] : Prop where
  uniformContinuous_star : UniformContinuous (star : α → α)

variable {α : Type*} [UniformSpace α]

section Star

variable [Star α]


instance : Star (UniformSpace.Completion α) :=
  ⟨Completion.map (fun a ↦ star a : α → α)⟩

lemma star_def [UniformContinuousStar α] (a : α) :
    star (↑a : Completion α) = ↑(star a) :=
  Completion.map_coe (hf := UniformContinuousStar.uniformContinuous_star) a


instance : ContinuousStar (Completion α) where
  continuous_star := by
    apply Completion.continuous_map

end Star

section InvolutiveStar

variable [InvolutiveStar α] [UniformContinuousStar α]

instance instInvolutiveStar : InvolutiveStar (UniformSpace.Completion α) where
  star_involutive := by
    intro x
    apply Completion.induction_on (p := fun x => star (star x) = x)
    · -- show the set {x | star (star x) = x} is closed
      exact isClosed_eq
        (continuous_star.comp (continuous_star : Continuous (star : Completion α → Completion α)))
        continuous_id
    · -- show that for each a : α, we have star (star (↑a)) = ↑a
      intro a
      simp only [star_def]
      rw [star_involutive a]

end InvolutiveStar

section StarAddMonoid

variable [AddGroup α] [StarAddMonoid α] [IsUniformAddGroup α]

#synth AddGroup (Completion α)

#check Continuous.prodMap



instance [UniformContinuousStar α] : StarAddMonoid (Completion α) where
  star_add := by
    intro r s
    apply Completion.induction_on₂ (p := fun x y => star (x + y) = star x + star y)
    · -- show IsClosed {x | star (x.1 + x.2) = star x.1 + star x.2}
      exact isClosed_eq
        (continuous_star.comp (continuous_add : Continuous (fun p : _ × _ => p.1 + p.2)))
        (continuous_add.comp (Continuous.prodMap continuous_star continuous_star))
    · -- show that for each a b : α, we have star (↑a + ↑b) = star (↑a) + star (↑b)
      intro a b
      rw [← Completion.coe_add]
      rw [star_def, star_def, star_def, star_add]
      rw [Completion.coe_add]

end StarAddMonoid

section StarMul

variable [Ring α] [StarMul α] [UniformContinuousStar α]
variable [IsTopologicalRing α] [IsUniformAddGroup α]

#synth Mul (Completion α)

instance : StarMul (Completion α) where
  star_mul := by
    intro r s
    apply Completion.induction_on₂ (p := fun x y => star (x * y) = star y * star x)
    · -- show IsClosed {x | star (x.1 * x.2) = star x.2 * star x.1}
      exact isClosed_eq
        (continuous_star.comp (continuous_mul : Continuous (fun p : _ × _ => p.1 * p.2)))
        (continuous_mul.comp
          (continuous_swap.comp (Continuous.prodMap continuous_star continuous_star)))
    · -- show that for each a b : α, we have star (↑a * ↑b) = star (↑b) * star (↑a)
      intro a b
      rw [← Completion.coe_mul]
      rw [star_def, star_def, star_def, star_mul]
      rw [Completion.coe_mul]

#synth StarMul (Completion α)

end StarMul

section StarRing

variable [Ring α] [StarRing α] [UniformContinuousStar α]
variable [IsTopologicalRing α] [IsUniformAddGroup α]

#synth StarAddMonoid α

#synth UniformSpace α

#synth Ring (Completion α)

#synth AddGroup α
#synth StarAddMonoid α

#synth StarAddMonoid (Completion α)

instance : StarRing (Completion α) where
  star_add := (inferInstance : StarAddMonoid (Completion α)).star_add

#synth StarRing (Completion α)

end StarRing

end
