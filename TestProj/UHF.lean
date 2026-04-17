import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Order.DirectedInverseSystem
import TestProj.CStar
import TestProj.amplify
import Mathlib.Analysis.CStarAlgebra.Hom

open Matrix
open scoped Matrix.Norms.L2Operator

section

variable {𝕜 n k : Type*}
variable [RCLike 𝕜] [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]

set_option backward.isDefEq.respectTransparency false in
example : CStarRing (Matrix n n 𝕜) := instCStarRing

#check amplify

set_option backward.isDefEq.respectTransparency false
#synth CStarRing (Matrix n n 𝕜)

#check instCStarRing
/-
NonUnitalNormedRing A, StarRing A, CompleteSpace A,
    CStarRing A, NormedSpace ℂ A, IsScalarTower ℂ A A, SMulCommClass ℂ A A, StarModule ℂ A
-/
#synth NonUnitalNormedRing (Matrix n n ℂ)
#synth StarRing (Matrix n n ℂ)
#synth CompleteSpace (Matrix n n ℂ)
#synth CStarRing (Matrix n n ℂ)
#synth NormedSpace ℂ (Matrix n n ℂ)
#synth SMul ℂ (Matrix n n ℂ)
#synth IsScalarTower ℂ (Matrix n n ℂ) (Matrix n n ℂ)
#synth SMulCommClass ℂ (Matrix n n ℂ) (Matrix n n ℂ)
#synth StarModule ℂ (Matrix n n ℂ)

--not sure why this is necessary...
noncomputable instance : CStarAlgebra (Matrix n n ℂ) where


#synth NonUnitalCStarAlgebra (Matrix n n ℂ)

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

--variable (F) in
def N : ℕ → Type u
  | 0 => F 0
  | n + 1 => (N n) × F (n + 1)

#check N F 3

abbrev G n := Matrix (N F n) (N F n) ℂ

variable (n : ℕ)
set_option trace.Meta.synthInstance true in
#synth Semiring (G F n)
#synth Fintype (F n)
#synth Fintype (N F n)


/-
instance : ∀ n, Fintype (N F n)
  | 0 => by
    change Fintype (F 0)
    infer_instance
  | n+1 => by
    change Fintype ((N F n) × F (n + 1))
    haveI : Fintype (N F n) := by infer_instance
    haveI : Fintype (F (n + 1)) := by infer_instance
    infer_instance
-/


instance : ∀ n, Fintype (N F n) := by
  intro n
  induction n with
  | zero => change Fintype (F 0); infer_instance
  | succ n ih =>
    unfold N -- change Fintype ((N F n) × F (n + 1))
    infer_instance

instance : ∀ n, DecidableEq (N F n) := by
  intro n
  induction n with
  | zero => change DecidableEq (F 0); infer_instance
  | succ n ih =>
    unfold N -- change DecidableEq ((N F n) × F (n + 1))
    infer_instance

instance : ∀ n, Nonempty (N F n) := by
  intro n
  induction n with
  | zero => change Nonempty (F 0); infer_instance
  | succ n ih =>
    unfold N -- change Nonempty ((N F n) × F (n + 1))
    infer_instance

#synth ∀ n, Semiring (Matrix (N F n) (N F n) ℂ) --now succeeds
#synth ∀ n, Algebra ℂ (Matrix (N F n) (N F n) ℂ)
#synth ∀ n, StarRing (Matrix (N F n) (N F n) ℂ)

#synth ∀ n, CStarRing (Matrix (N F n) (N F n) ℂ)

#synth ∀ n, Semiring (G F n)

#synth ∀ n, Semiring (G F n)
#synth ∀ n, Algebra ℂ (G F n)
#synth ∀ n, StarRing (G F n)
#synth ∀ n, NormedRing (G F n)
#synth ∀ n, CStarRing (G F n)
#synth ∀ n, CStarAlgebra (G F n)

/-
instance : ∀ n, Semiring (G F n) := by
  intro n
  change Semiring (Matrix (N F n) (N F n) ℂ)
  infer_instance

instance : ∀ n, Algebra ℂ (G F n) := by
  intro n
  change Algebra ℂ (Matrix (N F n) (N F n) ℂ)
  infer_instance


variable {F} in
noncomputable instance instStarRing {n : ℕ} : StarRing (G F n) := by
  --intro n
  unfold G
  change StarRing (Matrix (N F n) (N F n) ℂ)
  infer_instance


set_option trace.Meta.synthInstance true in
#synth ∀ i, StarRing (G F i)

set_option trace.Meta.synthInstance true in
#synth StarRing (G F 5)

set_option trace.Meta.synthInstance true in
noncomputable example (i : ℕ) : StarRing (G F i) := inferInstance

noncomputable instance (n : ℕ) : NormedRing (G F n) := by
  --intro n
  change NormedRing (Matrix (N F n) (N F n) ℂ)
  infer_instance

set_option diagnostics true
set_option trace.Meta.synthInstance true in
#synth StarRing (G F 5)


set_option trace.Meta.synthInstance true in
#synth StarRing (G F 0)
set_option trace.Meta.synthInstance true in
noncomputable example (i : ℕ) : StarRing (G F i) := inferInstance

noncomputable instance {n : ℕ} :
    --letI : ∀ n, StarRing (G F n) := fun n => instStarRing (n := n)
    letI : StarRing (G F n) := instStarRing (n := n)
    CStarRing (G F n) := by
  --intro n
  change CStarRing (Matrix (N F n) (N F n) ℂ)
  apply instCStarRing


noncomputable instance : ∀ n, CStarAlgebra (G F n) := by
  intro n
  change CStarAlgebra (Matrix (N F n) (N F n) ℂ)
  infer_instance

-/

#synth ∀ i, CStarAlgebra (G F i)

noncomputable def step (n : ℕ) : (G F n) →⋆ₐ[ℂ] (G F (n+1)) :=
  amplify (N F n) (F (n+1))

/-
noncomputable def hom : ∀ {n m : ℕ}, n ≤ m → G F n →⋆ₐ[ℂ] G F m
  | n, n,     le_rfl    => StarAlgHom.id ℂ (G F n)
  | n, m + 1, h         =>
      let h' : n ≤ m := Nat.le_of_lt_succ ?_
      (step F m).comp (hom F h')
-/

noncomputable def hom {n m : ℕ} (h : n ≤ m) : G F n →⋆ₐ[ℂ] G F m :=
  Nat.leRecOn (C := fun t => G F n →⋆ₐ[ℂ] G F t) h
    (fun {t} φ => (step F t).comp φ)
    (StarAlgHom.id ℂ (G F n))

/-
noncomputable def hom0 (n : ℕ) : ∀ m, n ≤ m → G F n →⋆ₐ[ℂ] G F m
  | n,     _ => StarAlgHom.id ℂ (G F n)
  | m + 1, h =>
      (step F m).comp (hom0 n m (Nat.le_of_lt_succ h))
-/

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

#check directedSystem

#check DirectLimit (G F) (fun _i _j hij => hom (F := F) hij)


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
      --rw [norm_amplify (N F j') (F (j' + 1)) ((hom F hij') x)]
      --rw [NonUnitalStarAlgHom.norm_map (φ := step F j') (amplify_injective _ _) ((hom F hij') x)]
      --exact NonUnitalStarAlgHom.norm_map (φ := step F j') (amplify_injective _ _) ((hom F hij') x)



#synth ∀ i, CStarRing (G F i)
#synth ∀ i, CStarAlgebra (G F i)


abbrev UHF_T {i j : ℕ} (hij : i ≤ j) := G F i →⋆ₐ[ℂ] G F j
noncomputable abbrev UHF_f (i j : ℕ) (hij : i ≤ j) : UHF_T F hij:= hom (F := F) hij
#check UHF_f

#check DirectLimit (G F) (UHF_f F)

#synth ∀ i j (hij : i ≤ j), FunLike (UHF_T F hij) (G F i) (G F j)
#synth ∀ i j h, StarHomClass (UHF_T F h) (G F i) (G F j)
#synth ∀ i j h, AlgHomClass (UHF_T F h) ℂ (G F i) (G F j)


#check DirectLimit.NormCompat (G F) (UHF_f F)
#synth DirectLimit.NormCompat (G F) (UHF_f F)

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


#check DirectLimit.instNormedRing (G := (G F)) (f := UHF_f F)
set_option trace.Meta.synthInstance true in
#synth NormedRing (DirectLimit (G F) (UHF_f F))
set_option trace.Meta.synthInstance true in
#synth (
  letI : DirectLimit.NormCompat (ι := ℕ)  (G F) (UHF_f F) := inferInstance
  letI : NormedRing (DirectLimit (ι := ℕ) (G F) (UHF_f F)) := DirectLimit.instNormedRing (G := (G F)) (f := UHF_f F)
  NormedRing (DirectLimit (ι := ℕ)  (G F) (UHF_f F)))

set_option trace.Meta.synthInstance true in
#synth (letI : DirectLimit.NormCompat (G F) (UHF_f F) := inferInstance
  letI := DirectLimit.instNormedRing (G := (G F)) (f := UHF_f F)
  letI : StarRing (DirectLimit (G F) (UHF_f F)) := DirectLimit.instStarRing_testProj
  CStarRing (DirectLimit (ι := ℕ) (G F) (UHF_f F)))
#synth @CStarRing (DirectLimit (G F) (UHF_f F)) (DirectLimit.instNonUnitalNormedRing (G := (G F)) (f := UHF_f F)) _

  /-
    apply Nat.leRecOn (C := fun k =>
  (hom (F := F) (Nat.le_trans hij ‹j ≤ k›) : G F i →⋆ₐ[ℂ] G F k) =
    (hom (F := F) ‹j ≤ k›).comp (hom (F := F) hij))
  -/




  /-
    induction hjk using Nat.le_induction with
  | base =>
      simp [hom_refl]
  | succ k hjk ih =>
      rw [hom_succ, hom_succ, ih]
      ext x
      rfl
  -/
  /-
    simp [Nat.leRecOn_trans hij hjk]
  let C := (fun {t} (φ : G F i →⋆ₐ[ℂ] G F t) ↦ (step F t).comp φ)
  rw [← hom_refl]
  -/

  --apply Nat.leRecOn (C := fun t => hom (F := F) (n := i) (m := t) = )
  -- induction on hjk using Nat.leRecOn


end UHF



section
universe u
variable {𝕜 n : Type u}
variable [RCLike 𝕜] [Fintype n] [DecidableEq n]

#synth StarRing (Matrix n n 𝕜)


example : StarRing (Matrix n n 𝕜) := by
  infer_instance

set_option backward.isDefEq.respectTransparency false in
example :
  haveI: StarRing (Matrix n n 𝕜) := instStarRing
  @CStarRing (Matrix n n 𝕜) _ inferInstance := instCStarRing


example : @CStarRing (Matrix n n 𝕜) _ instStarRing := instCStarRing
end


section wacko

universe uwacko

open Matrix
open scoped Matrix.Norms.L2Operator

#check instCStarRing

example (n : Type uwacko) [Fintype n] [DecidableEq n]
    (𝕜 : Type uwacko) [RCLike 𝕜] :
    @CStarRing (Matrix n n 𝕜) _ instStarRing := instCStarRing

end wacko


section wacko2

open Matrix
open scoped Matrix.Norms.L2Operator

universe uwacko2
variable {𝕜 n : Type uwacko2}
variable [kIsRCLike : RCLike 𝕜] [Fintype n] [DecidableEq n]

#check instCStarRing

example : @CStarRing (Matrix n n 𝕜) _ instStarRing := instCStarRing

--instance : @CStarRing (Matrix n n 𝕜) _ instStarRing := instCStarRing

#synth @CStarRing (Matrix n n 𝕜) _ instStarRing

end wacko2


section banana

universe u

variable {𝕜 n : Type u}

variable [kIsRCLike : RCLike 𝕜] [Fintype n] [DecidableEq n]

#check Matrix n n 𝕜

open Matrix
open scoped Matrix.Norms.L2Operator

#synth NormedAddCommGroup (Matrix n n 𝕜)

#check Matrix.instCStarRing




#check @RCLike.toStarRing

#synth StarRing 𝕜

--example [StarRing (Matrix n n 𝕜)]: CStarRing (Matrix n n 𝕜) := by
--  sorry

variable (n 𝕜) in
def foo1 := Matrix.instCStarRing (𝕜 := 𝕜) (n := n)

def foo := @Matrix.instCStarRing 𝕜 n _ _ _

#check foo

#check foo1 𝕜 n

#check Matrix.instStarRing

--local instance hack : StarRing (Matrix n n 𝕜) := sorry -- Matrix.instStarRing (n:= n) (α := 𝕜)

--set_option trace.Meta.synthInstance true in
set_option backward.isDefEq.respectTransparency false in
example : CStarRing (Matrix n n 𝕜) := Matrix.instCStarRing
set_option trace.Meta.synthInstance true in
local instance : CStarRing (Matrix n n 𝕜) := Matrix.instCStarRing


#synth Ring (Matrix n n 𝕜)
#synth StarRing (Matrix n n 𝕜) -- succeeds with `instStarRing`
#synth NonUnitalNormedRing (Matrix n n 𝕜) -- succeeds with `NormedRing.toNonUnitalNormedRing`



set_option trace.Meta.synthInstance true in
#synth CStarRing (Matrix n n 𝕜)

#check Matrix.instCStarRing

end banana
