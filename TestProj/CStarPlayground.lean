import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.RingTheory.MatrixAlgebra
import Mathlib.RingTheory.TensorProduct.Basic

#check SeminormedAddCommGroup
#check StarRing
#print StarRing
#print selfAdjoint
#print IsSelfAdjoint.norm_pow_two_pow
#print NormedRing

#check congrArg
#check edist

#print Function.Involutive

example {A : Type*}
    [SeminormedAddCommGroup A] [StarAddMonoid A] [NormedStarGroup A]
    (a : A) :
    ‖star a‖ = ‖a‖ := by
    simp only [norm_star]

example {A : Type*}
    [SeminormedAddCommGroup A] [StarAddMonoid A] [NormedStarGroup A]
    (a : A) :
    ‖star a‖₊ = ‖a‖₊ := by
    simp only [nnnorm_star]

example {A : Type*}
    [SeminormedAddCommGroup A] [StarAddMonoid A] [NormedStarGroup A]
    (a : A) :
    ‖star (star a)‖ = ‖a‖ :=
   congrArg norm (InvolutiveStar.star_involutive a)

example {A : Type*}
    [SeminormedAddCommGroup A] [StarAddMonoid A] [NormedStarGroup A] :
    Isometry (star : A → A) := by
    intros x1 x2
    rw [edist_dist, edist_dist, dist_eq_norm_sub, dist_eq_norm_sub, ← star_sub, norm_star]

example {A : Type*}
    [SeminormedAddCommGroup A] [StarAddMonoid A] [NormedStarGroup A]
    (a b : A) :
    dist (star a) (star b) = dist a b := by
    rw [dist_eq_norm_sub, dist_eq_norm_sub, ← star_sub, norm_star]

#check CStarRing.norm_mul_self_le

example {A : Type*}
    [NonUnitalNormedRing A] [StarRing A] [CStarRing A]
    (a : A) :
    ‖star a * a‖ = ‖a‖ * ‖a‖ := by
    apply le_antisymm
    swap
    · exact CStarRing.norm_mul_self_le a
    calc
      ‖star a * a‖ ≤ ‖star a‖ * ‖a‖ := norm_mul_le (star a) a
      _ = ‖a‖* ‖a‖ := by rw [norm_star]



lemma my_norm_star_mul_self {A : Type*}
    [NonUnitalNormedRing A] [StarRing A] [CStarRing A]
    (a : A) :
    ‖star a * a‖ = ‖a‖ * ‖a‖ := by
    refine le_antisymm ?ineq1 ?ineq2
    swap
    · exact CStarRing.norm_mul_self_le a
    calc
      ‖star a * a‖ ≤ ‖star a‖ * ‖a‖ := norm_mul_le (star a) a
      _ = ‖a‖* ‖a‖ := by rw [norm_star]

#check norm_star


#check star_involutive
#print Function.Involutive

example {A : Type*}
    [NonUnitalNormedRing A] [StarRing A] [CStarRing A]
    (a : A) :
    ‖a * star a‖ = ‖a‖ * ‖a‖ := by
  have h2 : ‖(star (star a)) * star a‖  = ‖a * star a‖ := by rw[star_involutive a]
  rw [← h2]
  have h3: ‖a‖ * ‖a‖ = ‖star a‖ * ‖star a‖ := by rw[norm_star]
  rw [h3]
  exact CStarRing.norm_star_mul_self (x:=star a)



/- # Part 4 — selfadjoint elements

These start to resemble operator algebra reasoning.
-/


example {A : Type*}
    [NonUnitalNormedRing A] [StarRing A] [CStarRing A]
    {a : A} (ha : IsSelfAdjoint a) :
    ‖a * a‖ = ‖a‖ * ‖a‖ := by
  have h : a * a = star a * a := by rw[ha]
  rw [h]
  exact my_norm_star_mul_self a


/-Try also:-/


example {A : Type*}
    [Star A]
    {a : A} (ha : IsSelfAdjoint a) :
    star a = a := ha



/- (This one is almost tautological, but it helps you learn how the definition unfolds.)

---

# Part 5 — weakening assumptions (good Lean training)

Start with something like:
-/
example {A : Type*}
    [NormedRing A] [StarRing A] [CStarRing A]
    (a : A) :
    ‖star a‖ = ‖a‖ := by
  sorry

/-
Then try **reducing the assumptions** until Lean stops compiling.
Your goal is to discover the **minimal typeclass assumptions** needed.

This exercise teaches you how mathlib’s hierarchy is structured.

---

# A slightly harder challenge

Try to prove this **without looking up the proof in mathlib**:


-/

example {A : Type*}
    [NonUnitalNormedRing A] [StarRing A] [CStarRing A]
    (a : A) :
    ‖star a * a‖ = ‖a * star a‖ := by
  sorry

/-You’ll probably want to use the previous C*-identity lemmas.
-/




#check (1 : Matrix (Fin 3) (Fin 3) ℂ)



open Matrix
open Kronecker

lemma mul_kronecker_one
    {n k : Type*} [Fintype n] [Fintype k] [DecidableEq k]
    (A B : Matrix n n ℂ) :
    (A * B) ⊗ₖ (1 : Matrix k k ℂ)  =
      (A ⊗ₖ (1 : Matrix k k ℂ)) * (B ⊗ₖ (1 : Matrix k k ℂ)) := by
    rw [show (1 : Matrix k k ℂ) = 1 * 1 by simp]
    rw [Matrix.mul_kronecker_mul A B 1 1]
    rw [← show (1 : Matrix k k ℂ) = 1 * 1 by simp]


example [Fintype m] [Fintype n] [NonUnitalNormedRing ℂ] [StarRing ℂ]
    (x : Matrix m m ℂ) (y : Matrix n n ℂ) :
    star (x ⊗ₖ y) = (star x) ⊗ₖ (star y) := by
    have h : (x ⊗ₖ y)ᴴ = xᴴ ⊗ₖ yᴴ := conjTranspose_kronecker x y
    rw [star_eq_conjTranspose, star_eq_conjTranspose, star_eq_conjTranspose]
    exact h

variable (mk : Type*) [Fintype mk] [DecidableEq mk]
variable (mk2 : Type*) [Fintype mk2] [DecidableEq mk2]

#check (inferInstance : Inhabited Nat)

#check Algebra ℂ (Matrix mk mk ℂ)
#synth Algebra ℂ (Matrix mk mk ℂ)

#check (inferInstance : Algebra ℂ (Matrix mk mk ℂ))
def foo : Algebra ℂ (Matrix mk mk ℂ):=
    inferInstance

#print Matrix.instAlgebra


def raw_amplify (n k : Type*) [Fintype n] [Fintype k] [DecidableEq k]
    (A : Matrix n n ℂ) : Matrix (n × k) (n × k) ℂ :=
    A ⊗ₖ (1 : Matrix k k ℂ)

noncomputable def amplify0
    (n k : Type*)
    [Fintype n] [DecidableEq n]
    [Fintype k] [DecidableEq k] :
    Matrix n n ℂ →⋆ₐ[ℂ] Matrix (n × k) (n × k) ℂ :=
{ toFun := fun A => A ⊗ₖ (1 : Matrix k k ℂ)

  map_one' := by
    simp

  map_zero' := by
    simp

  map_mul' := by
    intro A B
    simpa using
      (Matrix.mul_kronecker_mul A B
        (1 : Matrix k k ℂ) (1 : Matrix k k ℂ))

  map_add' := by
    intro A B
    simp [Matrix.add_kronecker]

  commutes' := by
    intro r
    ext ⟨i,a⟩ ⟨j,b⟩
    simp [kroneckerMap_apply, algebraMap_matrix_apply, one_apply, ← ite_and, and_comm]

  map_star' := by
    intro A
    --have h : star (1: Matrix k k ℂ) = 1 := by simp only [star_one]
    conv_lhs => rw[← star_one]
    rw [star_eq_conjTranspose, star_eq_conjTranspose, star_eq_conjTranspose,
    conjTranspose_kronecker]
}

#check Matrix.kroneckerStarAlgEquiv


open scoped TensorProduct

variable (mn : Type*) [Fintype mn] [DecidableEq mn]

#synth Semiring (Matrix mn mn ℂ)
#synth Algebra ℂ (Matrix mn mn ℂ)



#print Algebra.TensorProduct.instSemiring

/-
noncomputable instance : Semiring ((Matrix mn mn ℂ) ⊗[ℂ] (Matrix mk mk ℂ)) :=
    Algebra.TensorProduct.instSemiring

-/

/-
noncomputable instance myI (n k : Type*) [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
: Semiring ((Matrix n n ℂ) ⊗[ℂ] (Matrix k k ℂ)) :=
    @Algebra.TensorProduct.instSemiring ℂ (Matrix n n ℂ) (Matrix k k ℂ) _ _ _ _ _

#synth Semiring ((Matrix mn mn ℂ) ⊗[ℂ] (Matrix mk mk ℂ))

noncomputable instance myI2 (n k : Type*) [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
: Algebra ℂ ((Matrix n n ℂ) ⊗[ℂ] (Matrix k k ℂ)) :=
    Algebra.TensorProduct.instAlgebra

#synth Algebra ℂ ((Matrix mn mn ℂ) ⊗[ℂ] (Matrix mk mk ℂ))
-/




/-
noncomputable def amplify2
    (n k : Type*)
    [Fintype n] [DecidableEq n]
    [Fintype k] [DecidableEq k] :
    Matrix n n ℂ →⋆ₐ[ℂ] Matrix (n × k) (n × k) ℂ :=
  ((Matrix.kroneckerStarAlgEquiv n k ℂ):
  StarAlgHom ℂ ((Matrix n n ℂ) ⊗[ℂ] (Matrix k k ℂ)) (Matrix (n × k) (n × k) ℂ)).comp
    (StarAlgHom.ofAlgHom
      (Algebra.TensorProduct.includeLeft : Matrix n n ℂ →ₐ[ℂ]
        TensorProduct ℂ (Matrix n n ℂ) (Matrix k k ℂ)))


noncomputable def amplify3
    (n k : Type*)
    [Fintype n] [DecidableEq n]
    [Fintype k] [DecidableEq k] :
    Matrix n n ℂ →⋆ₐ[ℂ] Matrix (n × k) (n × k) ℂ :=
  (show ((Matrix n n ℂ ⊗[ℂ] Matrix k k ℂ) →⋆ₐ[ℂ] Matrix (n × k) (n × k) ℂ) from
      Matrix.kroneckerStarAlgEquiv n k ℂ).comp
    (StarAlgHom.ofAlgHom
      (Algebra.TensorProduct.includeLeft :
        Matrix n n ℂ →ₐ[ℂ] Matrix n n ℂ ⊗[ℂ] Matrix k k ℂ))
-/




-- set_option trace.Meta.synthInstance true in
noncomputable def amplify4
    (n k : Type*)
    [Fintype n] [DecidableEq n]
    [Fintype k] [DecidableEq k] :
    Matrix n n ℂ →⋆ₐ[ℂ] Matrix (n × k) (n × k) ℂ :=
{ toAlgHom :=
    (Matrix.kroneckerAlgEquiv n k ℂ).toAlgHom.comp
      (Algebra.TensorProduct.includeLeft :
        Matrix n n ℂ →ₐ[ℂ] Matrix n n ℂ ⊗[ℂ] Matrix k k ℂ)
  map_star' := by
    intro A
    -- prove:
    -- kroneckerAlgEquiv (star (A ⊗ₜ 1)) = star (kroneckerAlgEquiv (A ⊗ₜ 1))
    -- one way is to use the star-preservation theorem coming from kroneckerStarAlgEquiv
    simpa using
      (Matrix.kroneckerStarAlgEquiv n k ℂ).map_star' (A ⊗ₜ[ℂ] (1 : Matrix k k ℂ))
}


noncomputable def amplify5
    (n k : Type*)
    [Fintype n] [DecidableEq n]
    [Fintype k] [DecidableEq k] :
    Matrix n n ℂ →⋆ₐ[ℂ] Matrix (n × k) (n × k) ℂ :=
{ toAlgHom :=
    (Matrix.kroneckerStarAlgEquiv n k ℂ).toAlgEquiv.toAlgHom.comp
      (Algebra.TensorProduct.includeLeft :
        Matrix n n ℂ →ₐ[ℂ] Matrix n n ℂ ⊗[ℂ] Matrix k k ℂ)
  map_star' := by
    intro A
    simpa using
      (Matrix.kroneckerStarAlgEquiv n k ℂ).map_star' (A ⊗ₜ[ℂ] (1 : Matrix k k ℂ))
}

#check amplify4

open scoped TensorProduct



-- #check Matrix mn mn ℂ →ₐ[ℂ] Matrix mn mn ℂ ⊗[ℂ] Matrix mk mk ℂ

noncomputable def amplify7
    (n k : Type*)
    [Fintype n] [DecidableEq n]
    [Fintype k] [DecidableEq k] :
    Matrix n n ℂ →⋆ₐ[ℂ] Matrix (n × k) (n × k) ℂ :=
{ toAlgHom :=
    (Matrix.kroneckerStarAlgEquiv n k ℂ).toAlgEquiv.toAlgHom.comp
      (Algebra.TensorProduct.includeLeft :
        Matrix n n ℂ →ₐ[ℂ] Matrix n n ℂ ⊗[ℂ] Matrix k k ℂ)
  map_star' := by
    intro A
    simpa using
      (Matrix.kroneckerStarAlgEquiv n k ℂ).map_star'
        (A ⊗ₜ[ℂ] (1 : Matrix k k ℂ))
}


noncomputable def amplify
    (n k : Type*)
    [Fintype n] [DecidableEq n]
    [Fintype k] [DecidableEq k] :
    Matrix n n ℂ →⋆ₐ[ℂ] Matrix (n × k) (n × k) ℂ := by
    letI : Semiring ((Matrix n n ℂ) ⊗[ℂ] (Matrix k k ℂ)) :=
        @Algebra.TensorProduct.instSemiring ℂ (Matrix n n ℂ) (Matrix k k ℂ) _ _ _ _ _
    letI : Algebra ℂ ((Matrix n n ℂ) ⊗[ℂ] (Matrix k k ℂ)) :=
        Algebra.TensorProduct.instAlgebra
    exact
{
toAlgHom :=
    (Matrix.kroneckerStarAlgEquiv n k ℂ).toAlgEquiv.toAlgHom.comp
    (Algebra.TensorProduct.includeLeft :
        Matrix n n ℂ →ₐ[ℂ] Matrix n n ℂ ⊗[ℂ] Matrix k k ℂ)
map_star' := by
    intro A
    simpa using
    (Matrix.kroneckerStarAlgEquiv n k ℂ).map_star' (A ⊗ₜ[ℂ] (1 : Matrix k k ℂ))
}

#check amplify

@[simp] lemma amplify_apply
    (n k : Type*) [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
    (A : Matrix n n ℂ) :
    amplify n k A = A ⊗ₖ (1 : Matrix k k ℂ) := by
  simp only [amplify, toAlgEquiv_kroneckerStarAlgEquiv, AlgEquiv.toAlgHom_eq_coe,
    StarAlgHom.coe_mk', AlgHom.coe_comp, AlgHom.coe_coe, Function.comp_apply,
    kroneckerAlgEquiv_apply]
  have h :
    (Algebra.TensorProduct.includeLeft (R := ℂ) (S := ℂ)
      (A := Matrix n n ℂ) (B := Matrix k k ℂ) A)
    =
    A ⊗ₜ[ℂ] (1 : Matrix k k ℂ) :=
        (Algebra.TensorProduct.includeLeft_apply
          (R := ℂ) (S := ℂ)
          (A := Matrix n n ℂ) (B := Matrix k k ℂ) A)
  change
    kroneckerLinearEquiv n n k k ℂ
      (A ⊗ₜ[ℂ] (1 : Matrix k k ℂ))
      =
    A ⊗ₖ (1 : Matrix k k ℂ)
  rw [← h]
  exact
    (kroneckerLinearEquiv_tmul
    (l:= n) (m := n) (n := k) (p := k)
    (R := ℂ)
    A (1 : Matrix k k ℂ))
   -- simp [amplify, Algebra.TensorProduct.includeLeft_apply]
  -- rw [Algebra.TensorProduct.includeLeft_apply A]



noncomputable def amplify9
    (n k : Type*)
    [Fintype n] [DecidableEq n]
    [Fintype k] [DecidableEq k] :
    Matrix n n ℂ →⋆ₐ[ℂ] Matrix (n × k) (n × k) ℂ := by
    letI : Semiring ((Matrix n n ℂ) ⊗[ℂ] (Matrix k k ℂ)) :=
        @Algebra.TensorProduct.instSemiring ℂ (Matrix n n ℂ) (Matrix k k ℂ) _ _ _ _ _
    letI : Algebra ℂ ((Matrix n n ℂ) ⊗[ℂ] (Matrix k k ℂ)) :=
        Algebra.TensorProduct.instAlgebra
    let amplifyAlgHom : Matrix n n ℂ →ₐ[ℂ] Matrix (n × k) (n × k) ℂ :=
        (Matrix.kroneckerStarAlgEquiv n k ℂ).toAlgEquiv.toAlgHom.comp
        (Algebra.TensorProduct.includeLeft :
            Matrix n n ℂ →ₐ[ℂ] Matrix n n ℂ ⊗[ℂ] Matrix k k ℂ)
    exact
{
toAlgHom := amplifyAlgHom
map_star' := by
    intro A
    simpa using
    (Matrix.kroneckerStarAlgEquiv n k ℂ).map_star' (A ⊗ₜ[ℂ] (1 : Matrix k k ℂ))
}

#check amplify9


#check Equiv.prodAssoc mn mk mk2
#check Matrix.reindexAlgEquiv ℂ ℂ (Equiv.prodAssoc mn mk mk2)


#check (amplify4 (mn × mk) mk2).comp (amplify4 mn mk)
#check (amplify4 mn mk)
#check (amplify4 mn (mk × mk2)).toAlgHom
#check (Matrix.reindexAlgEquiv ℂ ℂ (Equiv.prodAssoc mn mk mk2)).toAlgHom


noncomputable def foo1 := ((amplify (mn × mk) mk2).comp (amplify mn mk)).toAlgHom
#check foo1

noncomputable def foo2 := (Matrix.reindexAlgEquiv ℂ ℂ (Equiv.prodAssoc mn mk mk2)).toAlgHom
#check foo2

noncomputable def foo3 := (foo2 mk mk2 mn).comp (foo1 mk mk2 mn)

#check foo3

noncomputable def foo4 := ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.prodAssoc mn mk mk2)).toAlgHom).comp
    (((amplify (mn × mk) mk2).comp (amplify mn mk)).toAlgHom)

#check foo4

noncomputable def foo5 := (amplify4 mn (mk × mk2)).toAlgHom
#check foo5

/-
have hkron1 : (1 : Matrix k k ℂ) ⊗ₖ (1 : Matrix k2 k2 ℂ) = (1 : Matrix (k × k2) (k × k2) ℂ)
    := one_kronecker_one
-/

lemma amplifyAssoc
    (n k k2 : Type*) [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
    [Fintype k2] [DecidableEq k2] :
    ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.prodAssoc n k k2)).toAlgHom).comp
      (((amplify (n × k) k2).comp (amplify n k)).toAlgHom) =
    (amplify n (k × k2)).toAlgHom := by
    ext A i j
    rcases i with ⟨i₁, i₂, i₃⟩
    rcases j with ⟨j₁, j₂, j₃⟩
    simp only [AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_comp, AlgHom.coe_coe, StarAlgHom.coe_toAlgHom,
      StarAlgHom.coe_comp, Function.comp_apply, amplify_apply, reindexAlgEquiv_apply, reindex_apply,
      submatrix_apply, Equiv.prodAssoc_symm_apply, kroneckerMap_apply]
    rw [one_apply, one_apply, one_apply, mul_boole, mul_boole, mul_boole]
    simp only [Prod.mk.injEq]
    rw [← ite_and]
    simp only [and_comm]

/-
    rw?
    simp only [hkron1, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_comp, AlgHom.coe_coe, StarAlgHom.coe_toAlgHom,
      StarAlgHom.coe_comp, Function.comp_apply, reindexAlgEquiv_apply, reindex_apply,
      submatrix_apply, Equiv.prodAssoc_symm_apply]
    rw?
    simp only [AlgHom.comp_apply, Matrix.reindexAlgEquiv_apply, Equiv.prodAssoc_apply,
      amplify, StarAlgHom.comp_apply, StarAlgHom.toAlgHom_apply]

-/
