import TopPowerProjection
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Exact

namespace SelfContainedCycle084
variable {F V W : Type*} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

/-- This is ker(z)/(ker(z) intersect range(z)), represented by its literal image
in V/range(z). No square-zero hypothesis is needed to define it. -/
abbrev qH (z : Module.End F V) : Submodule F (V ⧸ LinearMap.range z) :=
  (LinearMap.ker z).map (LinearMap.range z).mkQ

def qMk (z : Module.End F V) (v : V) (hv : z v=0) : qH z :=
  ⟨(LinearMap.range z).mkQ v,Submodule.mem_map_of_mem hv⟩

lemma q_induction (z : Module.End F V) (d : qH z) : ∃ v hv, d=qMk z v hv := by
  obtain ⟨_,⟨v,hv,rfl⟩⟩ := d
  exact ⟨v,hv,rfl⟩

variable (z : Module.End F V) (z' : Module.End F W) (f : V →ₗ[F] W)

def qMap (hf : ∀ v, f (z v)=z' (f v)) : qH z →ₗ[F] qH z' := by
  let fb := (LinearMap.range z).mapQ (LinearMap.range z') f (by
    rintro _ ⟨v,rfl⟩
    exact ⟨f v,(hf v).symm⟩)
  refine (fb.comp (qH z).subtype).codRestrict (qH z') ?_
  intro x
  obtain ⟨v,hv,rfl⟩ := q_induction z x
  change (LinearMap.range z').mkQ (f v)∈qH z'
  apply Submodule.mem_map_of_mem
  change z' (f v)=0
  rw [←hf,hv,map_zero]

@[simp] lemma qMap_mk (hf : ∀ v, f (z v)=z' (f v)) (v : V) (hv : z v=0) :
    qMap z z' f hf (qMk z v hv) = qMk z' (f v) (by rw [←hf,hv,map_zero]) := rfl

variable (P : Module.End F V) (hPz : P*z=0) (hzP : z*P=0)
  (hPP : P*P=P) (hdiff : ∀ v,z v=0 → v-P v∈LinearMap.range z)

def qToRange : qH z →ₗ[F] LinearMap.range P :=
  ((LinearMap.range z).liftQ P.rangeRestrict (by
    rintro _ ⟨v,rfl⟩
    apply Subtype.ext
    exact congrArg (fun L : Module.End F V => L v) hPz)).comp (qH z).subtype

def rangeToQ : LinearMap.range P →ₗ[F] qH z :=
  (((LinearMap.range z).mkQ).comp (LinearMap.range P).subtype).codRestrict (qH z) (by
    rintro ⟨v,x,hx⟩
    apply Submodule.mem_map_of_mem
    change z v=0
    rw [←hx]
    exact congrArg (fun L : Module.End F V => L x) hzP)

/-- Actual quotient maps in both directions; no equivalence is an input. -/
def qEquiv : qH z ≃ₗ[F] LinearMap.range P :=
  { qToRange z P hPz with
    invFun := rangeToQ z P hzP
    left_inv := by
      intro x
      obtain ⟨v,hv,rfl⟩ := q_induction z x
      apply Subtype.ext
      change (LinearMap.range z).mkQ (P v)=(LinearMap.range z).mkQ v
      rw [Submodule.mkQ_apply,Submodule.mkQ_apply,Submodule.Quotient.eq]
      simpa only [neg_sub] using (LinearMap.range z).neg_mem (hdiff v hv)
    right_inv := by
      intro x
      apply Subtype.ext
      change P x=x
      obtain ⟨v,hv⟩ := x.2
      rw [←hv]
      exact congrArg (fun L : Module.End F V => L v) hPP }

@[simp] lemma qEquiv_mk (v : V) (hv : z v=0) :
    (qEquiv z P hPz hzP hPP hdiff (qMk z v hv) : V)=P v := rfl

section Universal
variable {A U X Y Z : Type*} [Ring A]
  [AddCommGroup U] [Module F U] [AddCommGroup X] [Module F X]
  [AddCommGroup Y] [Module F Y] [AddCommGroup Z] [Module F Z]

/-- The main endpoint: top-power regularity in the actual acting algebra,
plus purity on one faithful object, implies exactness of the actual shifted
quotient on ALL representations. No purity/compatibility/equivalence premise
is imposed on the three objects of the exact complex. -/
theorem all_representation_q_exact
    (ρ : A →+* Module.End F U) (hfaith : Function.Injective ρ)
    (a b : A) {m : ℕ} (hm : 1≤m) (ha : a^(m+1)=0)
    (hi : a^m*b*a^m=a^m) (hpur : PureTop (ρ a) m)
    (τX : A →+* Module.End F X) (τY : A →+* Module.End F Y)
    (τZ : A →+* Module.End F Z) (f : X →ₗ[F] Y) (g : Y →ₗ[F] Z)
    (hf : ∀ c v, f (τX c v)=τY c (f v))
    (hg : ∀ c v, g (τY c v)=τZ c (g v)) (hex : Function.Exact f g) :
    Function.Exact (qMap (τX a) (τY a) f (hf a)) (qMap (τY a) (τZ a) g (hg a)) := by
  let P := topProjector a b m
  obtain ⟨hzX,hXz,hXX,hdX⟩ := all_representation_projection ρ hfaith a b hm ha hi hpur τX
  obtain ⟨hzY,hYz,hYY,hdY⟩ := all_representation_projection ρ hfaith a b hm ha hi hpur τY
  obtain ⟨hzZ,hZz,hZZ,hdZ⟩ := all_representation_projection ρ hfaith a b hm ha hi hpur τZ
  let eX := qEquiv (τX a) (τX P) hXz hzX hXX hdX
  let eY := qEquiv (τY a) (τY P) hYz hzY hYY hdY
  let eZ := qEquiv (τZ a) (τZ P) hZz hzZ hZZ hdZ
  have hF : ∀ x, (eY (qMap (τX a) (τY a) f (hf a) x) : Y)=f (eX x) := by
    intro x
    obtain ⟨v,hv,rfl⟩ := q_induction (τX a) x
    rw [qMap_mk]
    exact (hf P v).symm
  have hG : ∀ y, (eZ (qMap (τY a) (τZ a) g (hg a) y) : Z)=g (eY y) := by
    intro y
    obtain ⟨v,hv,rfl⟩ := q_induction (τY a) y
    rw [qMap_mk]
    exact (hg P v).symm
  intro y
  constructor
  · intro hy
    have hk : g (eY y)=0 := by
      rw [←hG,hy,map_zero]
      rfl
    obtain ⟨x,hx⟩ := (hex _).mp hk
    refine ⟨eX.symm ⟨τX P x,⟨x,rfl⟩⟩,?_⟩
    apply eY.injective
    apply Subtype.ext
    rw [hF,eX.apply_symm_apply]
    change f (τX P x)=(eY y:Y)
    rw [hf,hx]
    obtain ⟨v,hv⟩ := (eY y).2
    rw [←hv]
    exact congrArg (fun L : Module.End F Y => L v) hYY
  · rintro ⟨x,rfl⟩
    apply eZ.injective
    apply Subtype.ext
    rw [hG,hF,map_zero]
    exact (hex _).mpr ⟨(eX x:X),rfl⟩
end Universal
end SelfContainedCycle084
