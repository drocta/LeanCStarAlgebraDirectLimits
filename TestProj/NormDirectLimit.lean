import Mathlib.Order.DirectedInverseSystem
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Topology.MetricSpace.Isometry

namespace DirectLimit

variable {ι : Type*} [Preorder ι] {G : ι → Type*}
variable {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {f : ∀ _ _ h, T h}
variable [∀ i j (h : i ≤ j), FunLike (T h) (G i) (G j)] [DirectedSystem G (f · · ·)]
variable [IsDirectedOrder ι]

section norm

variable [∀ i, Norm (G i)] --[∀ i j h, NormHomClass (T h) (G i) (G j)]
variable (hnorm : ∀ i j h x, ‖(x : G i)‖ = ‖((f i j h) x : G j)‖)
--variable [∀ i, PseudoEMetricSpace (G i)]
-- variable [∀ i j h, Isometry (f i j h : G i → G j)]

instance instNorm : Norm (DirectLimit G f) where
  norm := DirectLimit.lift f (ih := fun i x => ‖ (x : G i)‖) hnorm --(fun _ _ _ _ => (hnorm _ _ _ _).symm)

#synth Norm (DirectLimit G f)
#check instNorm hnorm

example (hnorm : ∀ i j h x, ‖(x : G i)‖ = ‖((f i j h) x : G j)‖) :
    Norm (DirectLimit G f) := by
  letI := instNorm (f := f) hnorm
  infer_instance


lemma norm_def (hnorm : ∀ i j h x, ‖(x : G i)‖ = ‖((f i j h) x : G j)‖) (i : ι) (x : G i) :
    @Norm.norm _ (instNorm hnorm) (⟦⟨i, x⟩⟧ : DirectLimit G f) = ‖(x : G i)‖ := by
  have h := lift_def f (ih := fun i x => ‖ (x : G i)‖) hnorm ⟨i, x⟩
  simpa [h]



end norm

end DirectLimit
