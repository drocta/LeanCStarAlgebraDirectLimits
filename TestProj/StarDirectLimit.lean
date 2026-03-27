import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Algebra.Star.Basic
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

private lemma of_eq_of_le (i k : ι) (hik : i ≤ k) (x : G i) :
    (⟦⟨i, x⟩⟧ : DirectLimit G f) = ⟦⟨k, (f i k hik) x⟩⟧ :=
  eq_of_le (f := f) ⟨i, x⟩ k hik

section StarMul
variable [∀ i, Mul (G i)] [∀ i j h, MulHomClass (T h) (G i) (G j)]
variable [∀ i, StarMul (G i)] [∀ i j h, StarHomClass (T h) (G i) (G j)]

instance : StarMul (DirectLimit G f) where
  star_mul := by
    intro r s
    induction r using DirectLimit.induction with
    | ih i x => induction s using DirectLimit.induction with
      | ih j y =>
        obtain ⟨k, hik, hjk⟩ := directed_of (α := ι) (· ≤ ·) i j
        have star_r_eq_star_r' := of_eq_of_le (f := f) i k hik (star x)
        have star_s_eq_star_s' := of_eq_of_le (f := f) j k hjk (star y)
        have r_eq_r' := of_eq_of_le (f := f) i k hik x
        have s_eq_s' := of_eq_of_le (f := f) j k hjk y
        rw [star_def, star_def]
        rw [star_r_eq_star_r', star_s_eq_star_s', s_eq_s', r_eq_r']
        rw [mul_def, mul_def, map_star, map_star]
        rw [← star_mul, ← star_def]



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
    induction r using DirectLimit.induction with
    | ih i x => induction s using DirectLimit.induction with
      | ih j y =>
        obtain ⟨k, hik, hjk⟩ := directed_of (α := ι) (· ≤ ·) i j
        have star_r_eq_star_r' := of_eq_of_le (f := f) i k hik (star x)
        have star_s_eq_star_s' := of_eq_of_le (f := f) j k hjk (star y)
        have r_eq_r' := of_eq_of_le (f := f) i k hik x
        have s_eq_s' := of_eq_of_le (f := f) j k hjk y
        rw [star_def, star_def]
        rw [star_r_eq_star_r', star_s_eq_star_s', s_eq_s', r_eq_r']
        rw [add_def, add_def, map_star, map_star]
        rw [← star_add, ← star_def]

end StarAddMonoid

section StarRing
/- Reminder : `StarRing`s are not required to be unital. -/

variable [∀ i, NonUnitalNonAssocSemiring (G i)] [∀ i j h, NonUnitalRingHomClass (T h) (G i) (G j)]
variable [∀ i, StarRing (G i)] [∀ i j h, StarHomClass (T h) (G i) (G j)]
variable [Nonempty ι]
instance : StarRing (DirectLimit G f) where
  star_mul := by
    intro r s
    induction r using DirectLimit.induction with
    | ih i x => induction s using DirectLimit.induction with
      | ih j y =>
        obtain ⟨k, hik, hjk⟩ := directed_of (α := ι) (· ≤ ·) i j
        have star_r_eq_star_r' := of_eq_of_le (f := f) i k hik (star x)
        have star_s_eq_star_s' := of_eq_of_le (f := f) j k hjk (star y)
        have r_eq_r' := of_eq_of_le (f := f) i k hik x
        have s_eq_s' := of_eq_of_le (f := f) j k hjk y
        rw [star_def, star_def]
        rw [star_r_eq_star_r', star_s_eq_star_s', s_eq_s', r_eq_r']
        rw [mul_def, mul_def, map_star, map_star]
        rw [← star_mul, ← star_def]
  star_add := by
    intro r s
    induction r using DirectLimit.induction with
    | ih i x => induction s using DirectLimit.induction with
      | ih j y =>
        obtain ⟨k, hik, hjk⟩ := directed_of (α := ι) (· ≤ ·) i j
        have star_r_eq_star_r' := of_eq_of_le (f := f) i k hik (star x)
        have star_s_eq_star_s' := of_eq_of_le (f := f) j k hjk (star y)
        have r_eq_r' := of_eq_of_le (f := f) i k hik x
        have s_eq_s' := of_eq_of_le (f := f) j k hjk y
        rw [star_def, star_def]
        rw [star_r_eq_star_r', star_s_eq_star_s', s_eq_s', r_eq_r']
        rw [add_def, add_def, map_star, map_star]
        rw [← star_add, ← star_def]
end StarRing

section UnitalStarRing

/- Because I want to use the definition of `DirectLimit.Ring.of` and `DirectLimit.Ring.lift`,
   which require a unital ring structure,
   I am assuming that the rings in the directed system are unital,
   and that the morphisms are unital ring homomorphisms.
   This is despite the definition of `StarRing`, and most of the work done with `StarRing`s,
   not requiring unitality.
   Perhaps in the future a `DirectLimit.NonUnitalRing.of` and `DirectLimit.NonUnitalRing.lift`
   could be added, which would allow us to drop the unitality assumptions here. -/


variable [∀ i, NonAssocSemiring (G i)] [∀ i j h, RingHomClass (T h) (G i) (G j)]
variable [∀ i, StarRing (G i)] [∀ i j h, StarHomClass (T h) (G i) (G j)]
variable [Nonempty ι]

#synth StarRing (DirectLimit G f)
#synth NonUnitalNonAssocSemiring (DirectLimit G f)
#synth NonAssocSemiring (DirectLimit G f)

namespace UnitalStarRing





variable (G f) in
/-- The canonical map from a component to the direct limit. -/
noncomputable def of (i) : G i →⋆ₙ+* DirectLimit G f := {
  (DirectLimit.Ring.of G f i) with
  map_star' := by
    intro x
    -- I'll want to use star_def , but I need to go from `of` to `⟦⟨i, x⟩⟧`,
    -- so I need to show that `of i x = ⟦⟨i, x⟩⟧`
    have hx : (Ring.of G f i).toFun x = (⟦⟨i, x⟩⟧ : DirectLimit G f) := by rfl
    have hstarx : (Ring.of G f i).toFun (star x) = (⟦⟨i, star x⟩⟧ : DirectLimit G f) := by rfl
    rw [hx, hstarx, star_def]
}

@[simp] lemma of_f {i j} (hij) (x) : of G f j (f i j hij x) = of G f i x := .symm <| eq_of_le ..



variable (G f) in
/-- The canonical map from a component to the direct limit. -/
noncomputable def of2 (i) : G i →⋆ₙ+* DirectLimit G f where
  toFun x := ⟦⟨i, x⟩⟧
  map_mul' _ _ := (mul_def ..).symm
  map_add' _ _ := (add_def ..).symm
  map_zero' := (zero_def ..).symm
  map_star' _ := (star_def ..).symm


@[simp] lemma of2_f {i j} (hij) (x) : of2 G f j (f i j hij x) = of2 G f i x := .symm <| eq_of_le ..

/- bleh -/
structure UnitalStarRingHom (A B : Type*) [NonAssocSemiring A] [StarRing A] [NonAssocSemiring B]
    [StarRing B] extends A →⋆ₙ+* B where
  map_one' : toFun 1 = 1

variable {A B : Type*} [NonAssocSemiring A] [StarRing A] [NonAssocSemiring B] [StarRing B] in
instance : FunLike (UnitalStarRingHom A B) A B where
  coe f:= f.toFun
  coe_injective' := by rintro ⟨⟨⟨⟨f, _⟩, _⟩, _⟩, _⟩ ⟨⟨⟨⟨g, _⟩, _⟩, _⟩, _⟩ h; congr

/-
variable {A B : Type*} [NonAssocSemiring A] [StarRing A] [NonAssocSemiring B] [StarRing B] in
theorem UnitalStarRingHom.coe_toRingHom (f : UnitalStarRingHom A B) : ⇑f.toRingHom = f :=
  rfl
-/
variable {A B : Type*} [NonAssocSemiring A] [StarRing A] [NonAssocSemiring B] [StarRing B] in
def UnitalStarRingHom.toRingHom (f : UnitalStarRingHom A B) : A →+* B := {f with}

variable {A B : Type*} [NonAssocSemiring A] [StarRing A] [NonAssocSemiring B] [StarRing B] in
instance : RingHomClass (UnitalStarRingHom A B) A B where
  map_one f := f.map_one'
  map_mul f  := f.map_mul'
  map_zero f := f.map_zero'
  map_add f := f.map_add'

variable {A B : Type*} [NonAssocSemiring A] [StarRing A] [NonAssocSemiring B] [StarRing B] in
instance : StarHomClass (UnitalStarRingHom A B) A B where
  map_star f := f.map_star'


variable (A : Type*) [NonAssocSemiring A] [StarRing A]
variable (G f) in
/-- The universal property of the direct limit: maps from the components to another ring
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit.
-/
noncomputable def lift (g : ∀ i, UnitalStarRingHom (G i) A) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x) :
    DirectLimit G f →⋆ₙ+* A :=
  {(DirectLimit.Ring.lift G f A (g:= fun i => (g i).toRingHom) (Hg:=Hg)) with
    map_star' := DirectLimit.induction _ fun i x ↦ by
      simp_rw [star_def]--, lift_def, map_star (g i)]
      rw [lift_def]
    /-
    map_star' := by
      intro x
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
        MonoidHom.coe_coe]
      sorry
    -/

}

variable (G f) in
/-- The universal property of the direct limit: maps from the components to another ring
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit.
-/
noncomputable def lift2
    (g : ∀ i, UnitalStarRingHom (G i) A) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x) :
    DirectLimit G f →⋆ₙ+* A where
  toFun := _root_.DirectLimit.lift _ (g · ·) (fun i j hij x ↦ (Hg i j hij x).symm)
  --map_one' := by rw [one_def (Classical.arbitrary ι), lift_def, map_one]
  -- if we wanted a unital star ring homomorphismout, so of type `UnitalStarRingHom (DirectLimit G f) A`, we would include the above line
  map_mul' := DirectLimit.induction₂ _ fun i x y ↦ by simp_rw [mul_def, lift_def, map_mul (g i)]
  map_zero' := by simp_rw [zero_def (Classical.arbitrary ι), lift_def, map_zero]
  map_add' := DirectLimit.induction₂ _ fun i x y ↦ by simp_rw [add_def, lift_def, map_add (g i)]
  map_star' := DirectLimit.induction _ fun i x ↦ by simp_rw [star_def, lift_def, map_star (g i)]



end UnitalStarRing


end UnitalStarRing

section StarModule

variable {R : Type*} [Semiring R] [Star R]
variable [∀ i, Star (G i)] [∀ i j h, StarHomClass (T h) (G i) (G j)]
variable [∀ i, SMul R (G i)] [∀ i j h, MulActionHomClass (T h) R (G i) (G j)]
variable [∀ i, AddZero (G i)]
variable [∀ i, StarModule R (G i)] [∀ i j h, AddMonoidHomClass (T h) (G i) (G j)]

instance : StarModule R (DirectLimit G f) where
  star_smul := by
    intro r
    apply DirectLimit.induction
    intro i x
    rw [star_def, smul_def, smul_def, ← star_smul, star_def]

end StarModule



section Algebra
--variable {ι : Type*} [Preorder ι] {G : ι → Type*}
--variable {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {f : ∀ _ _ h, T h}
--variable [∀ i j (h : i ≤ j), FunLike (T h) (G i) (G j)] [DirectedSystem G (f · · ·)]
--variable [IsDirectedOrder ι]
variable [Nonempty ι]

variable {R : Type*} [CommSemiring R]
variable [∀ i, Ring (G i)] [∀ i j h, RingHomClass (T h) (G i) (G j)]
variable [∀ i, Algebra R (G i)] [∀ i j h, AlgHomClass (T h) R (G i) (G j)]

#synth Ring (DirectLimit G f)

-- variable [SMul R (DirectLimit G f)]


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
    rw [RingHom.map_one]
    rw [one_def]
    exact Classical.arbitrary ι
    intro i j hij
    rw [map_one, map_one, map_one]
  map_mul' := by
    intro r s
    rw [map₀_def, map₀_def, map₀_def]
    rw [mul_def]
    rw [map_mul]
    exact Classical.arbitrary ι
    intro i j hij
    rw [AlgHomClass.commutes]
    intro i j hij
    rw [AlgHomClass.commutes]
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


noncomputable instance : Algebra R (DirectLimit G f) where
  algebraMap := algebraMapAux
  commutes' := by
    intro r x
    rw [algebraMapAux_def]
    induction x using DirectLimit.induction with
      |ih i y =>
       let j := Classical.arbitrary ι
       obtain ⟨k, hik, hjk⟩ := directed_of (α := ι) (· ≤ ·) i j
       have x_eq_x' := of_eq_of_le (f := f) i k hik y
       have r_eq_r' := of_eq_of_le (f := f) j k hjk (algebraMap R (G j) r)
       rw [x_eq_x', r_eq_r']
       rw [mul_def, mul_def]
       let y' := (f i k hik) y
       rw [AlgHomClass.commutes]
       rw [Algebra.commutes (R:=R) (A := G k) r y']

  smul_def' := by
    intro r x
    induction x using DirectLimit.induction with
      |ih i y =>
        rw [smul_def]
        let j := Classical.arbitrary ι
        rw [algebraMapAux_def]
        obtain ⟨k, hik, hjk⟩ := directed_of (α := ι) (· ≤ ·) i j
        have r_eq_r' := of_eq_of_le (f := f) j k hjk (algebraMap R (G j) r)
        have x_eq_x' := of_eq_of_le (f := f) i k hik y
        have rx_eq_rx' := of_eq_of_le (f := f) i k hik (r • y)
        rw [r_eq_r', x_eq_x', rx_eq_rx']
        rw [mul_def, Algebra.smul_def']
        rw [map_mul (f := (f i k hik)) (Algebra.algebraMap r) y]
        have h : ∀ ℓ, (algebraMap R (G ℓ)) r = (Algebra.algebraMap (R:=R) (A := G ℓ)) r := by
          intro ℓ
          rfl
        rw [← h, AlgHomClass.commutes, AlgHomClass.commutes]

namespace Algebra

variable (G f) in
noncomputable def of2 (i : ι) : G i →ₐ[R] DirectLimit G f where
  toFun x := ⟦⟨i, x⟩⟧
  map_one' := (one_def i).symm
  map_mul' _ _ := (mul_def ..).symm
  map_add' _ _ := (add_def ..).symm
  map_zero' := (zero_def ..).symm
  commutes' := by
    intro r
    have h : (algebraMap R (DirectLimit G f)) = algebraMapAux := rfl
    rw [h]
    rw [algebraMapAux_def]
    let j := Classical.arbitrary ι
    obtain ⟨k, hik, hjk⟩ := directed_of (α := ι) (· ≤ ·) i j
    rw [of_eq_of_le (f := f) i k hik (algebraMap R (G i) r)]
    rw [of_eq_of_le (f := f) j k hjk (algebraMap R (G j) r)]
    rw [AlgHomClass.commutes, AlgHomClass.commutes]


variable (G f) in
noncomputable def of (i : ι) : G i →ₐ[R] DirectLimit G f :=
{(DirectLimit.Ring.of G f i) with
  commutes' := by
    intro r
    rw [RingHom.toFun_eq_coe]
    have h : (algebraMap R (DirectLimit G f)) = algebraMapAux := rfl
    rw [h]
    rw [algebraMapAux_def]
    let j := Classical.arbitrary ι
    obtain ⟨k, hik, hjk⟩ := directed_of (α := ι) (· ≤ ·) i j
    rw [show (DirectLimit.Ring.of G f i) (algebraMap R (G i) r)
          = (⟦⟨i, algebraMap R (G i) r⟩⟧ : DirectLimit G f) by rfl]
    rw [of_eq_of_le (f := f) i k hik (algebraMap R (G i) r)]
    rw [of_eq_of_le (f := f) j k hjk (algebraMap R (G j) r)]
    rw [AlgHomClass.commutes, AlgHomClass.commutes]
    /- alternatively:
    have hi :
      (⟦⟨i, algebraMap R (G i) r⟩⟧ : DirectLimit G f)
      = ⟦⟨k, (f i k hik) (algebraMap R (G i) r)⟩⟧ :=
      of_eq_of_le (f := f) i k hik (algebraMap R (G i) r)
    have hj :
      (⟦⟨j, algebraMap R (G j) r⟩⟧ : DirectLimit G f)
      = ⟦⟨k, (f j k hjk) (algebraMap R (G j) r)⟩⟧ :=
      of_eq_of_le (f := f) j k hjk (algebraMap R (G j) r)
    rw [show (DirectLimit.Ring.of G f i) (algebraMap R (G i) r)
        = (⟦⟨i, algebraMap R (G i) r⟩⟧ : DirectLimit G f) by rfl]
    rw [hj, hi]
    rw [AlgHomClass.commutes, AlgHomClass.commutes]
    -/

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

variable (g : ∀ i, G i →ₐ[R] A) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)
@[simp] theorem lift_of (i x) : lift G f A g Hg (of G f i x) = g i x := rfl


end Algebra


end Algebra

end DirectLimit
