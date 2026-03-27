import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Algebra.Star.Basic
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

/-
    calc
      DirectLimit.Ring.lift G f A (g := fun i => (g i).toRingHom) (Hg := Hg)
          (algebraMap R (DirectLimit G f) r)
          = DirectLimit.Ring.lift G f A (g := fun i => (g i).toRingHom) (Hg := Hg)
              ((DirectLimit.Algebra.of G f i) (algebraMap R (G i) r)) := by


    have h : (DirectLimit.Ring.lift G f A (g:= fun i => (g i).toRingHom) (Hg:=Hg)).toFun = _root_.DirectLimit.lift _ (g · ·) fun i j h x ↦ (Hg i j h x).symm := rfl
    let foo := _root_.DirectLimit.lift _ (g · ·) fun i j h x ↦ (Hg i j h x).symm
    intro r
    --rw [RingHom.toFun_eq_coe]
    rw [h]
    have Hg2 : ∀ i j hij x, (g i).toRingHom x = (g j).toRingHom (f i j hij x) := by
      intro i j hij x
      simp [Hg]
    have h2 := lift_def (F:=G) f (fun i => (g i).toRingHom) Hg2
    rw [h2]
    rw [lift_def]
    simp
    sorry
-/



end Algebra


end Algebra

end DirectLimit
