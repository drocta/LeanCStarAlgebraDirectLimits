import Mathlib.Analysis.CStarAlgebra.Basic

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



example {A : Type*}
    [NonUnitalNormedRing A] [StarRing A] [CStarRing A]
    (a : A) :
    ‖star a * a‖ = ‖a‖ * ‖a‖ := by
    refine le_antisymm ?ineq1 ?ineq2
    swap
    · exact CStarRing.norm_mul_self_le a
    calc
      ‖star a * a‖ ≤ ‖star a‖ * ‖a‖ := norm_mul_le (star a) a
      _ = ‖a‖* ‖a‖ := by rw [norm_star]


example {A : Type*}
    [NonUnitalNormedRing A] [StarRing A] [CStarRing A]
    (a : A) :
    ‖a * star a‖ = ‖a‖ * ‖a‖ := by
  sorry


/- # Part 4 — selfadjoint elements

These start to resemble operator algebra reasoning.
-/


example {A : Type*}
    [NonUnitalNormedRing A] [StarRing A] [CStarRing A]
    {a : A} (ha : IsSelfAdjoint a) :
    ‖a * a‖ = ‖a‖ * ‖a‖ := by
  sorry


/-Try also:-/


example {A : Type*}
    [StarSemiring A]
    {a : A} (ha : IsSelfAdjoint a) :
    star a = a := by
  sorry


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
