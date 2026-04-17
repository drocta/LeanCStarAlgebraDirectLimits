import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.RingTheory.MatrixAlgebra
/-
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.RingTheory.MatrixAlgebra
import Mathlib.RingTheory.TensorProduct.Basic
-/




open scoped TensorProduct
open scoped Kronecker

variable {𝕜 : Type*} [RCLike 𝕜]

noncomputable def amplify
  (n k : Type*)
  [Fintype n] [DecidableEq n]
  [Fintype k] [DecidableEq k] :
  Matrix n n 𝕜 →⋆ₐ[𝕜] Matrix (n × k) (n × k) 𝕜 := by
  letI : Semiring ((Matrix n n 𝕜) ⊗[𝕜] (Matrix k k 𝕜)) :=
    @Algebra.TensorProduct.instSemiring 𝕜 (Matrix n n 𝕜) (Matrix k k 𝕜) _ _ _ _ _
  letI : Algebra 𝕜 ((Matrix n n 𝕜) ⊗[𝕜] (Matrix k k 𝕜)) :=
    Algebra.TensorProduct.instAlgebra
  exact
  {
  toAlgHom :=
    (Matrix.kroneckerStarAlgEquiv n k 𝕜).toAlgEquiv.toAlgHom.comp
    (Algebra.TensorProduct.includeLeft :
      Matrix n n 𝕜 →ₐ[𝕜] Matrix n n 𝕜 ⊗[𝕜] Matrix k k 𝕜)
  map_star' := by
    intro A
    simpa using
    (Matrix.kroneckerStarAlgEquiv n k 𝕜).map_star' (A ⊗ₜ[𝕜] (1 : Matrix k k 𝕜))
  }

@[simp] lemma amplify_apply
    (n k : Type*) [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
    (A : Matrix n n 𝕜) :
    amplify n k A = A ⊗ₖ (1 : Matrix k k 𝕜) := by
  simp only [amplify, Matrix.toAlgEquiv_kroneckerStarAlgEquiv, AlgEquiv.toAlgHom_eq_coe,
    StarAlgHom.coe_mk', AlgHom.coe_comp, AlgHom.coe_coe, Function.comp_apply,
    Matrix.kroneckerAlgEquiv_apply]
  exact
    (kroneckerLinearEquiv_tmul
    (l:= n) (m := n) (n := k) (p := k)
    (R := 𝕜)
    A (1 : Matrix k k 𝕜))


lemma amplify_alg_assoc
  (n k k2 : Type*) [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
  [Fintype k2] [DecidableEq k2] :
  ((Matrix.reindexAlgEquiv 𝕜 𝕜 (Equiv.prodAssoc n k k2)).toAlgHom).comp
    (((amplify (n × k) k2).comp (amplify n k)).toAlgHom) =
  (amplify n (k × k2)).toAlgHom := by
  ext A
  have h := Matrix.kronecker_assoc A (1 : Matrix k k 𝕜) (1 : Matrix k2 k2 𝕜)
  simp [amplify_apply, h]


-- @[simp]
lemma amplify_one
  (n k : Type*) [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k] :
  amplify n k (1 : Matrix n n 𝕜) = (1 : Matrix (n × k) (n × k) 𝕜) := by
  exact (amplify n k).map_one

lemma amplify_apply_apply
  (n k : Type*) [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
  (A : Matrix n n 𝕜) (i j : n) (a b : k) :
  (amplify n k A) (i, a) (j, b) = (if a = b then A i j else 0) := by
  simp only [amplify_apply, Matrix.kroneckerMap_apply]
  rw [Matrix.one_apply, mul_boole]


lemma amplify_injective
  (n k : Type*) [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k] [Nonempty k] :
  Function.Injective (amplify (𝕜 := 𝕜) n k) := by
  intro A B h
  ext i j
  let d : k := Classical.choice ‹Nonempty k›
  have h' : (amplify n k) A (i, d) (j, d) = (amplify n k) B (i, d) (j, d) :=
    congrArg (fun f => f (i, d) (j, d)) h
  simp only [amplify_apply_apply, ↓reduceIte] at h'
  exact h'



namespace Matrix

section StarAlg

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
variable (R A : Type*) [CommSemiring R] [Semiring A] [Star A] [Algebra R A]

/-- For square matrices with coefficients in a star algebra over a commutative semiring, the natural
map that reindexes a matrix's rows and columns with equivalent types,
`Matrix.reindex`, is an equivalence of star algebras. -/
def reindexStarAlgEquiv (e : m ≃ n) : Matrix m m A ≃⋆ₐ[R] Matrix n n A :=
  {(Matrix.reindexAlgEquiv R A e).toRingEquiv with
    toFun := reindex e e
    map_smul' :=  by
      intro r M
      ext i j
      rfl
    map_star' := by
      intro M
      ext i j
      rfl
  }

@[simp] theorem reindexStarAlgEquiv_apply (e : m ≃ n) (M : Matrix m m A) :
    reindexStarAlgEquiv R A e M = Matrix.reindex e e M :=
  rfl

end StarAlg

end Matrix


lemma amplify_assoc_reindex
  (n k k2 : Type*) [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
  [Fintype k2] [DecidableEq k2] :
  ((Matrix.reindexStarAlgEquiv 𝕜 𝕜 (Equiv.prodAssoc n k k2)) : _ →⋆ₐ[𝕜] _).comp
    ((amplify (n × k) k2).comp (amplify n k)) =
  amplify n (k × k2) := by
  ext A
  have h := Matrix.kronecker_assoc A (1 : Matrix k k 𝕜) (1 : Matrix k2 k2 𝕜)
  simp [amplify_apply, h]


lemma amplify_assoc
  (n k k2 : Type*) [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
  [Fintype k2] [DecidableEq k2] :
  ((amplify (n × k) k2).comp (amplify n k)) =
    ((Matrix.reindexStarAlgEquiv 𝕜 𝕜 (Equiv.prodAssoc n k k2).symm) : _ →⋆ₐ[𝕜] _).comp
      (amplify n (k × k2)) := by
    let e := ((Matrix.reindexStarAlgEquiv 𝕜 𝕜 (Equiv.prodAssoc n k k2)))
    let e₂ : Matrix (n × k × k2) (n × k × k2) 𝕜 →⋆ₐ[𝕜] Matrix ((n × k) × k2) ((n × k) × k2) 𝕜 := e.symm
    have h := @amplify_assoc_reindex 𝕜 _ n k k2 _ _ _ _ _ _
    have h1 := congrArg (fun φ => (e₂.comp φ)) h
    exact h1



lemma amplify_assoc2
  (n k k2 : Type*) [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
  [Fintype k2] [DecidableEq k2] :
  ((amplify (n × k) k2).comp (amplify n k)) =
    ((Matrix.reindexStarAlgEquiv 𝕜 𝕜 (Equiv.prodAssoc n k k2).symm) : _ →⋆ₐ[𝕜] _).comp
      (amplify n (k × k2)) := by
  have h := @amplify_assoc_reindex 𝕜 _ n k k2 _ _ _ _ _ _
  simpa using
    congrArg
      (fun φ =>
        (((Matrix.reindexStarAlgEquiv 𝕜 𝕜 (Equiv.prodAssoc n k k2)).symm :
        _ →⋆ₐ[𝕜] Matrix ((n × k) × k2) ((n × k) × k2) 𝕜).comp φ))
      h

lemma amplify_assoc3
  (n k k2 : Type*) [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
  [Fintype k2] [DecidableEq k2] :
  ((amplify (n × k) k2).comp (amplify n k)) =
    ((Matrix.reindexStarAlgEquiv 𝕜 𝕜 (Equiv.prodAssoc n k k2).symm) : _ →⋆ₐ[𝕜] _).comp
      (amplify n (k × k2)) := by
  let e :
      Matrix (n × (k × k2)) (n × (k × k2)) 𝕜 →⋆ₐ[𝕜]
        Matrix ((n × k) × k2) ((n × k) × k2) 𝕜 :=
    (Matrix.reindexStarAlgEquiv 𝕜 𝕜 (Equiv.prodAssoc n k k2)).symm
  have h := @amplify_assoc_reindex 𝕜 _ n k k2 _ _ _ _ _ _
  simpa using congrArg (fun φ => (e.comp φ)) h

private def StarAlgEquiv.toStarAlgHom {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Star A] [Star B] [Algebra R A] [Algebra R B]
    (e : A ≃⋆ₐ[R] B) : A →⋆ₐ[R] B :=
  (e : A →⋆ₐ[R] B)


lemma amplify_assoc4
  (n k k2 : Type*) [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
  [Fintype k2] [DecidableEq k2] :
  ((amplify (n × k) k2).comp (amplify n k)) =
    ((Matrix.reindexStarAlgEquiv 𝕜 𝕜 (Equiv.prodAssoc n k k2).symm) : _ →⋆ₐ[𝕜] _).comp
      (amplify n (k × k2)) := by
  let e := (Matrix.reindexStarAlgEquiv 𝕜 𝕜 (Equiv.prodAssoc n k k2)).symm.toStarAlgHom
  have h := @amplify_assoc_reindex 𝕜 _ n k k2 _ _ _ _ _ _
  simpa using congrArg (fun φ => (e.comp φ)) h

lemma amplify_assoc_manualIndexTwiddling
    (n k k2 : Type*) [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
    [Fintype k2] [DecidableEq k2] :
    (amplify (n × k) k2).comp (amplify n k) =
      ((Matrix.reindexStarAlgEquiv 𝕜 𝕜 (Equiv.prodAssoc n k k2).symm) : _ →⋆ₐ[𝕜] _).comp
        (amplify n (k × k2)) := by
  ext A
  simp [amplify_apply, Matrix.one_apply, ← ite_and, and_comm]
