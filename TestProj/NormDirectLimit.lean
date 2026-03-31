import Mathlib.Order.DirectedInverseSystem
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Algebra.Colimit.DirectLimit

namespace DirectLimit

variable {ι : Type*} [Preorder ι] {G : ι → Type*}
variable {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {f : ∀ _ _ h, T h}
variable [∀ i j (h : i ≤ j), FunLike (T h) (G i) (G j)] [DirectedSystem G (f · · ·)]
variable [IsDirectedOrder ι]

section norm

variable [∀ i, Norm (G i)] --[∀ i j h, NormHomClass (T h) (G i) (G j)]
variable (hnorm : ∀ i j h x, ‖(x : G i)‖ = ‖((f i j h) x : G j)‖)

instance instNorm : Norm (DirectLimit G f) where
  norm := DirectLimit.lift f (ih := fun i x => ‖ (x : G i)‖) hnorm

-- #synth Norm (DirectLimit G f)
#check instNorm hnorm

example (hnorm : ∀ i j h x, ‖(x : G i)‖ = ‖((f i j h) x : G j)‖) :
    Norm (DirectLimit G f) := by
  letI := instNorm hnorm
  infer_instance


lemma norm_def0 (hnorm : ∀ i j h x, ‖(x : G i)‖ = ‖((f i j h) x : G j)‖) (i : ι) (x : G i) :
    @Norm.norm _ (instNorm hnorm) (⟦⟨i, x⟩⟧ : DirectLimit G f) = ‖(x : G i)‖ := by
  simpa using (lift_def f (ih := fun i x => ‖ (x : G i)‖) hnorm ⟨i, x⟩)

lemma norm_def (hnorm : ∀ i j h x, ‖(x : G i)‖ = ‖((f i j h) x : G j)‖) (i : ι) (x : G i) :
    letI : Norm (DirectLimit G f) := instNorm hnorm
    ‖ (⟦⟨i, x⟩⟧ : DirectLimit G f)‖ = ‖(x : G i)‖ := by
  simpa using (lift_def f (ih := fun i x => ‖ (x : G i)‖) hnorm ⟨i, x⟩)



lemma norm_lift {α : Type*} [Norm α] (hnorm) (g : ∀ i, G i → α)
    (Hg : ∀ i j h x, (g i x = g j ((f i j h) x)))
    (hg_norm : ∀ i x, ‖g i x‖ = ‖(x : G i)‖) :
    letI : Norm (DirectLimit G f) := instNorm hnorm
    (∀ z : DirectLimit G f, ‖DirectLimit.lift f g Hg z‖ = ‖z‖) := by
  apply DirectLimit.induction
  intro i x
  rw [lift_def, norm_def]
  simp only [hg_norm]

end norm



section NormedAddGroup

variable [Nonempty ι]

variable [∀ i, NormedAddGroup (G i)]
variable (hnorm : ∀ i j h x, ‖(x : G i)‖ = ‖((f i j h) x : G j)‖)
variable [∀ i j h, AddMonoidHomClass (T h) (G i) (G j)]

set_option diagnostics true in
#synth AddGroup (DirectLimit G f)

noncomputable instance instMetricSpaceOfNormedAddGroup
    (hnorm : ∀ i j h x, ‖(x : G i)‖ = ‖((f i j h) x : G j)‖) :
    MetricSpace (DirectLimit G f) := by
  letI : Norm (DirectLimit G f) := instNorm hnorm
  exact {
    dist := fun x y => ‖x - y‖
    dist_self := by
      apply DirectLimit.induction (C := fun x => ‖x - x‖ = 0)
      intro i y
      rw [sub_def, norm_def]
      rw[← NormedAddGroup.dist_eq, dist_self]
    dist_comm := by
      apply DirectLimit.induction₂ (C := fun x y => ‖x - y‖ = ‖y - x‖)
      intro i x y
      rw [sub_def, sub_def, norm_def, norm_def]
      rw [← NormedAddGroup.dist_eq, ← NormedAddGroup.dist_eq, dist_comm]
    dist_triangle := by
      apply DirectLimit.induction₃ (C := fun x y z => ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖)
      intro i x y z
      rw [sub_def, sub_def, sub_def, norm_def, norm_def, norm_def]
      rw [← NormedAddGroup.dist_eq, ← NormedAddGroup.dist_eq, ← NormedAddGroup.dist_eq]
      apply dist_triangle
    eq_of_dist_eq_zero := by
      apply DirectLimit.induction₂ (C := fun x y => ‖x - y‖ = 0 → x = y)
      intro i x y h
      rw [sub_def, norm_def] at h
      rw [← NormedAddGroup.dist_eq] at h
      have h' : x = y := eq_of_dist_eq_zero (x := x) (y := y) h
      rw [h']
  }

noncomputable instance instNormedAddGroupOfNormedAddGroup
    (hnorm : ∀ i j h x, ‖(x : G i)‖ = ‖((f i j h) x : G j)‖) :
    NormedAddGroup (DirectLimit G f) := by
  letI := instNorm hnorm
  letI := instMetricSpaceOfNormedAddGroup hnorm
  exact {}


#check instNormedAddGroupOfNormedAddGroup hnorm


end NormedAddGroup


section NormedAddCommGroup

variable [Nonempty ι]

variable [∀ i, NormedAddCommGroup (G i)]
variable (hnorm : ∀ i j h x, ‖(x : G i)‖ = ‖((f i j h) x : G j)‖)
variable [∀ i j h, AddMonoidHomClass (T h) (G i) (G j)]


noncomputable instance instNormedAddCommGroupOfNormedAddCommGroup
    (hnorm : ∀ i j h x, ‖(x : G i)‖ = ‖((f i j h) x : G j)‖) :
    NormedAddCommGroup (DirectLimit G f) := by
  letI := instNorm hnorm
  letI := instMetricSpaceOfNormedAddGroup hnorm
  exact {}

#check instNormedAddCommGroupOfNormedAddCommGroup hnorm

end NormedAddCommGroup


end DirectLimit
