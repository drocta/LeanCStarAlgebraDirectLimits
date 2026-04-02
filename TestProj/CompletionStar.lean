import Mathlib.Topology.Algebra.Star
import Mathlib.Topology.Algebra.GroupCompletion
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Topology.Constructions.SumProd


noncomputable section

open UniformSpace

variable {α : Type*} [UniformSpace α]

section Star

variable [Star α]
variable (hstar : UniformContinuous (star : α → α))

instance : Star (UniformSpace.Completion α) :=
  ⟨Completion.map (fun a ↦ star a : α → α)⟩

#check @hstar


lemma star_def (hstar : UniformContinuous (star : α → α)) (a : α) :
    star (↑a : Completion α) = ↑(star a) :=  Completion.map_coe (hf := hstar) a


instance : ContinuousStar (Completion α) where
  continuous_star := by
    apply Completion.continuous_map

end Star

section InvolutiveStar

variable [InvolutiveStar α]
variable (hstar : UniformContinuous (star : α → α))

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
      simp only [star_def hstar]
      rw [star_involutive a]


end InvolutiveStar

section StarAddGroup

variable [AddGroup α] [StarAddMonoid α] [IsUniformAddGroup α]

#synth AddGroup (Completion α)

#check Continuous.prodMap

lemma uniformContinuous_star : UniformContinuous (star : α → α) := by
  have h := @IsUniformAddGroup.uniformContinuous_sub α _ _ _
  apply uniform_continuous_of_continuous
  exact continuous_star

--#synth InvolutiveStar (Completion α)

instance : StarAddMonoid (Completion α) := by
  have hstar : UniformContinuous (star : α → α) := by
    sorry
  exact {
    star_add := by
      intro r s
      apply Completion.induction_on₂ (p := fun x y => star (x + y) = star x + star y)
      · -- show IsClosed {x | star (x.1 + x.2) = star x.1 + star x.2}
        exact isClosed_eq
          (continuous_star.comp (continuous_add : Continuous (fun p : _ × _ => p.1 + p.2)))
          (continuous_add.comp (Continuous.prodMap continuous_star continuous_star))
        --apply continuous_add.comp (Continuous.prodMap continuous_star continuous_star)
          --(continuous_add.comp (continuous_star.prod_mk continuous_star))
      /-
          apply Completion.map₂ (fun a b ↦ star (a + b) : α → α → α)
      intro a₁ a₂ b₁ b₂
      rw [star_add, star_add]
      -/
      · -- show that for each a b : α, we have star (↑a + ↑b) = star (↑a) + star (↑b)
        intro a b
        rw [← Completion.coe_add]
        rw [star_def hstar, star_def hstar, star_def hstar, star_add]
        rw [Completion.coe_add]


    star_involutive := by
      letI : InvolutiveStar (Completion α) := instInvolutiveStar hstar
      exact star_involutive
  }

end StarAddGroup



end
