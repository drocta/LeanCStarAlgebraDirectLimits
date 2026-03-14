import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Defs

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

noncomputable def amplify
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
