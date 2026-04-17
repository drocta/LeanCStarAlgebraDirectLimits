import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Order.DirectedInverseSystem
import TestProj.CStar
import TestProj.amplify
import Mathlib.Analysis.CStarAlgebra.Hom

open Matrix
open scoped Matrix.Norms.L2Operator

section

variable {n : Type*}
variable [Fintype n] [DecidableEq n]

set_option backward.isDefEq.respectTransparency false in
noncomputable instance : CStarAlgebra (Matrix n n ℂ) where


/- This proof is specific to square matrices over complex numbers,
and relies on them forming a C*-algebra.
This might be better to have in a more general way (for `(Matrix n n 𝕜)` instead)
but I think the proof for that would require some work about
the norm of tensor products of linear maps,
which isn't in mathlib yet,
and my interest is mostly in the complex case, so for now this is good enough. -/
lemma norm_amplify
    (n k : Type*)
    [Fintype n] [DecidableEq n]
    [Fintype k] [DecidableEq k] [Nonempty k]
    (A : Matrix n n ℂ) :
    ‖amplify n k A‖ = ‖A‖ := by
  have h_inj : Function.Injective (amplify n k : Matrix n n ℂ → Matrix (n × k) (n × k) ℂ) :=
    amplify_injective n k
  exact NonUnitalStarAlgHom.norm_map (amplify n k) h_inj A


/-
--TODO : a version for matrices over more general RCLike fields would be nice.
lemma norm_amplify (A : Matrix n n 𝕜) :
    ‖amplify n k A‖ = ‖A‖ := by
  rw [Matrix.cstar_norm_def, Matrix.cstar_norm_def]
  sorry
  simp only [amplify_apply]--, norm_kronecker, norm_one]
  --rw [@kronecker_one]
  rw [@cstar_norm_def]
  rw?
  exact norm_mul_eq_left A (1 : Matrix n n 𝕜)
-/


end

section UHF
universe u
variable (F : ℕ → Type u)
variable [∀ n, Fintype (F n)] [∀ n, DecidableEq (F n)] [∀ n, Nonempty (F n)]

namespace UHF.MatrixSystem

def N : ℕ → Type u
  | 0 => F 0
  | n + 1 => (N n) × F (n + 1)


abbrev G n := Matrix (N F n) (N F n) ℂ


instance : ∀ n, Fintype (N F n) := by
  intro n
  induction n with
  | zero => change Fintype (F 0); infer_instance
  | succ n ih =>
    change Fintype ((N F n) × F (n + 1)) -- obtained by `unfold N`
    infer_instance

instance : ∀ n, DecidableEq (N F n) := by
  intro n
  induction n with
  | zero => change DecidableEq (F 0); infer_instance
  | succ n ih =>
    change DecidableEq ((N F n) × F (n + 1)) -- `unfold N` also works here
    infer_instance

instance : ∀ n, Nonempty (N F n) := by
  intro n
  induction n with
  | zero => change Nonempty (F 0); infer_instance
  | succ n ih =>
    change Nonempty ((N F n) × F (n + 1)) -- `unfold N` also works here
    infer_instance

#synth ∀ n, Semiring (G F n)

#synth ∀ n, Semiring (G F n)
#synth ∀ n, Algebra ℂ (G F n)
#synth ∀ n, StarRing (G F n)
#synth ∀ n, NormedRing (G F n)
#synth ∀ n, CStarRing (G F n)
#synth ∀ n, CStarAlgebra (G F n)


noncomputable def step (n : ℕ) : (G F n) →⋆ₐ[ℂ] (G F (n+1)) :=
  amplify (N F n) (F (n+1))

noncomputable def hom {n m : ℕ} (h : n ≤ m) : G F n →⋆ₐ[ℂ] G F m :=
  Nat.leRecOn (C := fun t => G F n →⋆ₐ[ℂ] G F t) h
    (fun {t} φ => (step F t).comp φ)
    (StarAlgHom.id ℂ (G F n))



omit [∀ (n : ℕ), Nonempty (F n)] in
lemma hom_refl (n : ℕ) :
    hom (F := F) (n := n) (m := n) le_rfl = StarAlgHom.id ℂ (G F n) := by
  unfold hom
  rw [Nat.leRecOn_self]

omit [∀ (n : ℕ), Nonempty (F n)] in
lemma hom_succ {n m : ℕ} (h : n ≤ m) :
    hom (F := F) (Nat.le_succ_of_le h) =
      (step F m).comp (hom (F := F) h) := by
  unfold hom
  apply Nat.leRecOn_succ

omit [∀ (n : ℕ), Nonempty (F n)] in
lemma hom_trans {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    (hom (F := F) (Nat.le_trans hij hjk) : G F i →⋆ₐ[ℂ] G F k) =
      (hom (F := F) hjk).comp (hom (F := F) hij) := by
  induction hjk using Nat.leRec with
  | refl => rw [hom_refl, StarAlgHom.id_comp]
  | le_succ_of_le hjk ih =>
    rw [hom_succ (F := F) (h := Nat.le_trans hij hjk)]
    rw [ih]
    rw [hom_succ (F := F) (h := hjk)]
    rfl


omit [∀ (n : ℕ), Nonempty (F n)] in
instance directedSystem : DirectedSystem (G F) (fun _i _j hij => hom (F := F) hij) where
  map_self := by
    intro i x
    rw [hom_refl (F := F) i]
    simp
  map_map := by
    intro i j k hij hjk x
    rw [hom_trans (F := F) hij hjk]
    simp


#check DirectLimit (G F) (fun _i _j hij => hom (F := F) hij)

--this one actually uses the hypothesis that the F n are nonempty.
lemma norm_hom (i j : ℕ) (hij : i ≤ j) (x : G F i) :
    ‖(hom (F := F) hij x : G F j)‖ = ‖(x : G F i)‖ := by
  induction hij using Nat.leRec with
  | refl =>
      rw [hom_refl]
      simp
  | @le_succ_of_le j' hij' ih =>
      have h := hom_succ (F := F) (h := hij')
      rw [h]
      rw [← ih]
      rw [StarAlgHom.comp_apply]
      --unfold step
      exact norm_amplify (N F j') (F (j' + 1)) ((hom F hij') x)


abbrev UHF_T {i j : ℕ} (hij : i ≤ j) := G F i →⋆ₐ[ℂ] G F j
noncomputable abbrev UHF_f (i j : ℕ) (hij : i ≤ j) : UHF_T F hij:= hom (F := F) hij
#check UHF_f

#check DirectLimit (G F) (UHF_f F)

#synth ∀ i j (hij : i ≤ j), FunLike (UHF_T F hij) (G F i) (G F j)
#synth ∀ i j h, StarHomClass (UHF_T F h) (G F i) (G F j)
#synth ∀ i j h, AlgHomClass (UHF_T F h) ℂ (G F i) (G F j)


#check DirectLimit.NormCompat (G F) (UHF_f F)

variable {F} in
instance normCompat : DirectLimit.NormCompat (G F) (UHF_f F) where
  norm_compat := by
    intro i j h x
    exact (norm_hom F i j h x).symm

#synth DirectLimit.NormCompat (G F) (UHF_f F)

#synth Norm (DirectLimit (G F) (UHF_f F))
#synth Star (DirectLimit (G F) (UHF_f F))
#synth StarRing (DirectLimit (G F) (UHF_f F))
#synth ∀ i, NormedRing (G F i)
#synth ∀ i, StarRing (G F i)
#synth NormedRing (DirectLimit (G F) (UHF_f F))
#synth CStarRing (DirectLimit (G F) (UHF_f F))

open UniformSpace
#synth CStarAlgebra (Completion (DirectLimit (G F) (UHF_f F)))

end UHF.MatrixSystem

end UHF
