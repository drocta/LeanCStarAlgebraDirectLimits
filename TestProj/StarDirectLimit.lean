import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Algebra.Star.StarRingHom
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Hom

namespace DirectLimit

variable {ι : Type*} [Preorder ι] {G : ι → Type*}
variable {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {f : ∀ _ _ h, T h}
variable [∀ i j (h : i ≤ j), FunLike (T h) (G i) (G j)] [DirectedSystem G (f · · ·)]
variable [IsDirectedOrder ι]

section Star
variable [∀ i, Star (G i)] [∀ i j h, StarHomClass (T h) (G i) (G j)]
instance : Star (DirectLimit G f) where
  star := DirectLimit.map f f (fun _ x => star x) (compat := by
    intro i j h
    exact StarHomClass.map_star (f i j h)
  )



lemma star_def (i : ι) (x : G i) :
    star ⟦⟨i, x⟩⟧ = (⟦⟨i, star x ⟩⟧ : DirectLimit G f) := by
  rfl



end Star

section InvolutiveStar
variable [∀ i, InvolutiveStar (G i)] [∀ i j h, StarHomClass (T h) (G i) (G j)]
instance : InvolutiveStar (DirectLimit G f) where
  star_involutive := by
    apply DirectLimit.induction
    intro i x
    rw [star_def, star_def, star_star]

end InvolutiveStar


section StarMul
variable [∀ i, Mul (G i)] [∀ i j h, MulHomClass (T h) (G i) (G j)]
variable [∀ i, StarMul (G i)] [∀ i j h, StarHomClass (T h) (G i) (G j)]

instance : StarMul (DirectLimit G f) where
  star_mul := by
    intro r s
    induction r, s using DirectLimit.induction₂ with
    | ih i x y =>
      rw [mul_def, star_def, star_def, star_def, star_mul, mul_def]

end StarMul

section StarAddMonoid

variable [∀ i, AddMonoid (G i)] [∀ i j h, AddMonoidHomClass (T h) (G i) (G j)]
variable [∀ i, StarAddMonoid (G i)] [∀ i j h, StarHomClass (T h) (G i) (G j)]

/- we need [Nonempty ι] in order to be able to synthesize an instance of AddMonoid
using DirectLimit.instAddMonoid-/
variable [Nonempty ι]

instance : StarAddMonoid (DirectLimit G f) where
  star_add := by
    intro r s
    induction r, s using DirectLimit.induction₂ with
    | ih i x y =>
      rw [add_def, star_def, star_def, star_def, add_def, star_add]

end StarAddMonoid

section StarRing
/- Reminder : `StarRing`s are not required to be unital. -/

variable [∀ i, NonUnitalNonAssocSemiring (G i)] [∀ i j h, NonUnitalRingHomClass (T h) (G i) (G j)]
variable [∀ i, StarRing (G i)] [∀ i j h, StarHomClass (T h) (G i) (G j)]
variable [Nonempty ι]
instance : StarRing (DirectLimit G f) where
  star_mul := by
    intro r s
    induction r, s using DirectLimit.induction₂ with
    | ih i x y =>
      rw [mul_def, star_def, star_def, star_def, mul_def, star_mul]
  star_add := by
    intro r s
    induction r, s using DirectLimit.induction₂ with
    | ih i x y =>
      rw [add_def, star_def, star_def, star_def, add_def, star_add]


namespace StarRing

variable (G f) in
/-- The canonical map from a component to the direct limit. -/
noncomputable def of (i) : G i →⋆ₙ+* DirectLimit G f where
  toFun x := ⟦⟨i, x⟩⟧
  map_mul' _ _ := (mul_def ..).symm
  map_add' _ _ := (add_def ..).symm
  map_zero' := (zero_def ..).symm
  map_star' _ := (star_def ..).symm

@[simp] lemma of_f {i j} (hij) (x) : of G f j (f i j hij x) = of G f i x := .symm <| eq_of_le ..

variable (A : Type*) [NonUnitalNonAssocSemiring A] [StarRing A]
variable (G f) in
/-- The universal property of the direct limit: maps from the components to another ring
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit.
-/
noncomputable def lift
    (g : ∀ i, (G i) →⋆ₙ+* A) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x) :
    DirectLimit G f →⋆ₙ+* A where
  toFun := _root_.DirectLimit.lift _ (g · ·) (fun i j hij x ↦ (Hg i j hij x).symm)
  --map_one' := by rw [one_def (Classical.arbitrary ι), lift_def, map_one] --non-unital, so no need
  map_mul' := DirectLimit.induction₂ _ fun i x y ↦ by simp_rw [mul_def, lift_def, map_mul (g i)]
  map_zero' := by simp_rw [zero_def (Classical.arbitrary ι), lift_def, map_zero]
  map_add' := DirectLimit.induction₂ _ fun i x y ↦ by simp_rw [add_def, lift_def, map_add (g i)]
  map_star' := DirectLimit.induction _ fun i x ↦ by simp_rw [star_def, lift_def, map_star (g i)]


variable (g : ∀ i, G i →⋆ₙ+* A) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

@[simp] theorem lift_of (i x) : lift G f A g Hg (of G f i x) = g i x := rfl

end StarRing

end StarRing

section StarModule

variable {R : Type*} [Semiring R] [Star R]
variable [∀ i, Star (G i)] [∀ i j h, StarHomClass (T h) (G i) (G j)]
variable [∀ i, SMul R (G i)] [∀ i j h, MulActionHomClass (T h) R (G i) (G j)]
variable [∀ i, StarModule R (G i)]

instance : StarModule R (DirectLimit G f) where
  star_smul := by
    intro r
    apply DirectLimit.induction
    intro i x
    rw [star_def, smul_def, smul_def, ← star_smul, star_def]

end StarModule


private lemma of_eq_of_le (i k : ι) (hik : i ≤ k) (x : G i) :
    (⟦⟨i, x⟩⟧ : DirectLimit G f) = ⟦⟨k, (f i k hik) x⟩⟧ :=
  eq_of_le (f := f) ⟨i, x⟩ k hik

-- TODO: add support for non-unital algebras
section Algebra

variable [Nonempty ι]

variable {R : Type*} [CommSemiring R]
variable [∀ i, Semiring (G i)] [∀ i j h, RingHomClass (T h) (G i) (G j)]
variable [∀ i, Algebra R (G i)] [∀ i j h, AlgHomClass (T h) R (G i) (G j)]




/- TODO: Perhaps all the places I use `Classical.arbitrary ι` could instead be using
`DirectLimit.map₀` and `DirectLimit.map₀_def`-/
noncomputable def algebraMapAux : R →+* DirectLimit G f :={
    toFun := fun r => ⟦⟨Classical.arbitrary ι, algebraMap R (G (Classical.arbitrary ι)) r⟩⟧
    map_one' := by
      simp only [algebraMap]
      rw [RingHom.map_one]
      rfl
    map_mul' := by
      intro r s
      simp only [algebraMap]
      rw [mul_def]
      simp only [map_mul]
    map_add' := by
      intro r s
      simp only [algebraMap, add_def, map_add]
    map_zero' := by
      simp only [algebraMap, map_zero]
      exact zero_def (f:=f) (Classical.arbitrary ι)
  }

/- an attempt at defining the algebra map via DirectLimit.map₀ , which I thought would be simpler,
  and maybe more idiomatic, but it turned out longer,
  perhaps because I'm not using map₀_def correctly.
  Also, the linter is mad about how I'm dealing with multiple goals-/
noncomputable def algebraMapAux2 :  R →+* DirectLimit G f := {
  toFun r := DirectLimit.map₀ f (fun i => algebraMap R (G i ) r)
  map_one' := by
    rw [map₀_def]
    · --first goal
      rw [RingHom.map_one]
      rw [one_def]
      exact Classical.arbitrary ι
    · --second goal: compatibility between the directed system maps and the algebra maps
      intro i j hij
      rw [map_one, map_one, map_one]
  map_mul' := by
    intro r s
    rw [map₀_def, map₀_def, map₀_def]
    · --first goal
      rw [mul_def]
      · --subgoal
        rw [map_mul]
      · --subgoal : entry from ι
        exact Classical.arbitrary ι
    · --first instance of the compatibility goal
      intro i j hij
      rw [AlgHomClass.commutes]
    · --second instance of the compatibility goal
      intro i j hij
      rw [AlgHomClass.commutes]
    · --third instance of the compatibility goal
      intro i j hij
      rw [AlgHomClass.commutes]
  map_zero' := by
    rw [map₀_def]
    rw [RingHom.map_zero]
    rw [zero_def]
    exact Classical.arbitrary ι
    intro i j hij
    rw [map_zero, map_zero, map_zero]
  map_add' := by
    intro r s
    rw [map₀_def, map₀_def, map₀_def]
    rw [add_def, map_add]
    exact Classical.arbitrary ι
    intro i j hij
    rw [AlgHomClass.commutes]
    intro i j hij
    rw [AlgHomClass.commutes]
    intro i j hij
    rw [AlgHomClass.commutes]
}


lemma algebraMapAux2_def (r : R) :
  algebraMapAux2 (R:=R) r
  = (⟦⟨Classical.arbitrary ι, algebraMap R (G (Classical.arbitrary ι)) r⟩⟧ : DirectLimit G f) :=
  rfl

omit [∀ (i j : ι) (h : i ≤ j), AlgHomClass (T h) R (G i) (G j)] in
lemma algebraMapAux_def (r : R) :
    algebraMapAux (R:=R) r
      = (⟦⟨Classical.arbitrary ι, algebraMap R (G (Classical.arbitrary ι)) r⟩⟧ : DirectLimit G f) :=
      rfl

lemma algebraMapAux_at (i : ι) (r : R) :
    algebraMapAux (R:=R) r
      = (⟦⟨i, algebraMap R (G i) r⟩⟧ : DirectLimit G f) := by
  let j := Classical.arbitrary ι
  rw [algebraMapAux_def]
  obtain ⟨k, hik, hjk⟩ := directed_of (α := ι) (· ≤ ·) i j
  rw [of_eq_of_le (f := f) j k hjk (algebraMap R (G j) r)]
  rw [of_eq_of_le (f := f) i k hik (algebraMap R (G i) r)]
  rw [AlgHomClass.commutes, AlgHomClass.commutes]


noncomputable instance : Algebra R (DirectLimit G f) where
  algebraMap := algebraMapAux
  commutes' := by
    intro r x
    induction x using DirectLimit.induction with
      |ih i y =>
        rw [algebraMapAux_at i, mul_def, mul_def, Algebra.commutes]

  smul_def' := by
    intro r x
    induction x using DirectLimit.induction with
      |ih i y =>
        rw [smul_def]
        let j := Classical.arbitrary ι
        rw [algebraMapAux_at i, mul_def, Algebra.smul_def']
        rfl

lemma algebraMap_at (i : ι) (r : R) :
    algebraMap R (DirectLimit G f) r = (⟦⟨i, algebraMap R (G i) r⟩⟧ : DirectLimit G f) := by
  rw [← algebraMapAux_at i]
  rfl

namespace Algebra

variable (G f) in
noncomputable def of2 (i : ι) : G i →ₐ[R] DirectLimit G f where
  toFun x := ⟦⟨i, x⟩⟧
  map_one' := (one_def i).symm
  map_mul' _ _ := (mul_def ..).symm
  map_add' _ _ := (add_def ..).symm
  map_zero' := (zero_def ..).symm
  commutes' := by intro r; rw [algebraMap_at i]

variable (G f) in
noncomputable def of (i : ι) : G i →ₐ[R] DirectLimit G f :=
{(DirectLimit.Ring.of G f i) with
  commutes' := by
    intro r
    rw [RingHom.toFun_eq_coe]
    rw [algebraMap_at i]
    rw [show (DirectLimit.Ring.of G f i) (algebraMap R (G i) r)
          = (⟦⟨i, algebraMap R (G i) r⟩⟧ : DirectLimit G f) by rfl]
}

variable (A : Type*) [Semiring A] [Algebra R A]

variable (G f) in
/-- The universal property of the direct limit: maps from the components to another R-algebra
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit.
-/
noncomputable def lift (g : ∀ i, G i →ₐ[R] A) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x) :
    DirectLimit G f →ₐ[R] A :=
{(DirectLimit.Ring.lift G f A (g:= fun i => (g i).toRingHom) (Hg:=Hg)) with
  commutes' := by
    let i := Classical.arbitrary ι
    intro r
    let of := Algebra.of G f i
    let ring_of := of.toRingHom
    let algMap_limit := algebraMap R (DirectLimit G f)
    let algMap_Gi := algebraMap R (G i)
    let algMap_A := algebraMap R A
    let lift := DirectLimit.Ring.lift G f A (g:= fun i => (g i).toRingHom) (Hg:=Hg)
    have lift_of : lift (ring_of (algMap_Gi r)) = (g i).toRingHom (algMap_Gi r) :=
      DirectLimit.Ring.lift_of A (g:= fun i => (g i).toRingHom) Hg i (algMap_Gi r)
    calc
      lift (algMap_limit r) = lift (of (algMap_Gi r)) := by rw [AlgHom.commutes]
      _ = lift (ring_of (algMap_Gi r)) := by rfl
      _ = (g i).toRingHom (algMap_Gi r) := lift_of
      _ = (g i) (algMap_Gi r) := by rfl
      _ = algMap_A r := by rw [AlgHom.commutes]
}


variable (G f) in
/-- The universal property of the direct limit: maps from the components to another R-algebra
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit.
-/
noncomputable def lift2 (g : ∀ i, G i →ₐ[R] A) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x) :
    DirectLimit G f →ₐ[R] A where
  toFun := _root_.DirectLimit.lift _ (g · ·) fun i j h x ↦ (Hg i j h x).symm
  map_one' := by rw [one_def (Classical.arbitrary ι), lift_def, map_one]
  map_mul' := DirectLimit.induction₂ _ fun i x y ↦ by simp_rw [mul_def, lift_def, map_mul]
  map_zero' := by simp_rw [zero_def (Classical.arbitrary ι), lift_def, map_zero]
  map_add' := DirectLimit.induction₂ _ fun i x y ↦ by simp_rw [add_def, lift_def, map_add]
  commutes' := by
    let i := Classical.arbitrary ι
    intro r
    let of := Algebra.of G f i
    let ring_of := of.toRingHom
    let algMap_limit := algebraMap R (DirectLimit G f)
    let algMap_Gi := algebraMap R (G i)
    let algMap_A := algebraMap R A
    let lift := DirectLimit.Ring.lift G f A (g:= fun i => (g i).toRingHom) (Hg:=Hg)
    have lift_of : lift (ring_of (algMap_Gi r)) = (g i).toRingHom (algMap_Gi r) :=
      DirectLimit.Ring.lift_of A (g:= fun i => (g i).toRingHom) Hg i (algMap_Gi r)
    calc
      lift (algMap_limit r) = lift (of (algMap_Gi r)) := by rw [AlgHom.commutes]
      _ = lift (ring_of (algMap_Gi r)) := by rfl
      _ = (g i).toRingHom (algMap_Gi r) := lift_of
      _ = (g i) (algMap_Gi r) := by rfl
      _ = algMap_A r := by rw [AlgHom.commutes]

variable (g : ∀ i, G i →ₐ[R] A) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)
@[simp] theorem lift_of (i x) : lift G f A g Hg (of G f i x) = g i x := rfl

@[simp] theorem lift2_of2 (i x) : lift2 G f A g Hg (of2 G f i x) = g i x := rfl


end Algebra


end Algebra



section StarAlgebra

variable {R : Type*} [CommSemiring R] [StarRing R]
variable [∀ i, Semiring (G i)]
variable [∀ i, StarRing (G i)]
variable [∀ i, Algebra R (G i)]
variable [∀ i, StarModule R (G i)]
variable [∀ i j h, StarHomClass (T h) (G i) (G j)]
variable [∀ i j h, AlgHomClass (T h) R (G i) (G j)]
variable [∀ i j h, MulActionHomClass (T h) R (G i) (G j)]

variable [Nonempty ι]


#synth Star (DirectLimit G f)
#synth StarModule R (DirectLimit G f)
#synth StarRing (DirectLimit G f)
#synth Semiring (DirectLimit G f)
#synth Algebra R (DirectLimit G f)

end StarAlgebra


section NonUnitalStarAlgebra


variable {R : Type*} [CommSemiring R] [StarRing R]
variable [∀ i, NonUnitalNonAssocSemiring (G i)]
variable [∀ i, StarRing (G i)]
variable [∀ i, DistribMulAction R (G i)]
variable [∀ i, StarModule R (G i)]
variable [∀ i j h, StarHomClass (T h) (G i) (G j)]
variable [∀ i j h, NonUnitalRingHomClass (T h) (G i) (G j)]
variable [∀ i j h, MulActionHomClass (T h) R (G i) (G j)]

variable [Nonempty ι]


#synth Star (DirectLimit G f)
#synth StarModule R (DirectLimit G f)
#synth NonUnitalNonAssocSemiring (DirectLimit G f)
#synth StarRing (DirectLimit G f)
#synth SMul R (DirectLimit G f)


end NonUnitalStarAlgebra


end DirectLimit
