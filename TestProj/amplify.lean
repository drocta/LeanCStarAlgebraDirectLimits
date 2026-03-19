import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.RingTheory.MatrixAlgebra
import Mathlib.RingTheory.TensorProduct.Basic



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

lemma amplify_assoc
  (n k k2 : Type*) [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
  [Fintype k2] [DecidableEq k2] :
  ((Matrix.reindexAlgEquiv 𝕜 𝕜 (Equiv.prodAssoc n k k2)).toAlgHom).comp
    (((amplify (n × k) k2).comp (amplify n k)).toAlgHom) =
  (amplify n (k × k2)).toAlgHom := by
  ext A
  have h := Matrix.kronecker_assoc A (1 : Matrix k k 𝕜) (1 : Matrix k2 k2 𝕜)
  simp [amplify_apply, h]
