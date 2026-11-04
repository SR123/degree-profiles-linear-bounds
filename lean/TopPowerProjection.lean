import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic

namespace SelfContainedCycle084

/-- Successive elimination, in the actual acting algebra. -/
def stages {A : Type*} [Ring A] (z w : A) (m : ℕ) : ℕ → A
  | 0 => 1
  | k+1 => (1-z^k*w*z^(m-k))*stages z w m k

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- The kernel/range purity condition excludes intermediate nilpotent strings. -/
def PureTop (z : Module.End F V) (m : ℕ) : Prop :=
  ∀ v, z v=0 → v∈LinearMap.range z → v∈LinearMap.range (z^m)

lemma top_inverse_on_range {u w : Module.End F V} (h : u*w*u=u)
    {v : V} (hv : v∈LinearMap.range u) : u (w v)=v := by
  obtain ⟨x,rfl⟩ := hv
  exact congrArg (fun f : Module.End F V => f x) h

lemma elimination_step (z w R : Module.End F V) {m d : ℕ} (hd : 1≤d) (hdm : d≤m)
    (hpur : PureTop z m) (hi : z^m*w*z^m=z^m) (hz : z^(d+1)*R=0) :
    z^d*((1-z^(m-d)*w*z^d)*R)=0 := by
  have hpow : z^d*z^(m-d)=z^m := by rw [←pow_add,Nat.add_sub_of_le hdm]
  calc
    z^d*((1-z^(m-d)*w*z^d)*R) = (z^d-(z^d*z^(m-d))*w*z^d)*R := by noncomm_ring
    _ = (z^d-z^m*w*z^d)*R := by rw [hpow]
    _ = 0 := by
      ext v
      have hk : z ((z^d) (R v))=0 := by
        have hh := congrArg (fun f : Module.End F V => f v) hz
        simpa only [pow_succ',Module.End.mul_apply,LinearMap.zero_apply] using hh
      have hr : (z^d) (R v)∈LinearMap.range z := by
        refine ⟨(z^(d-1)) (R v),?_⟩
        have hd' : d-1+1=d := by omega
        rw [←Module.End.mul_apply,←pow_succ',hd']
      have ht := top_inverse_on_range hi (hpur _ hk hr)
      simpa only [Module.End.mul_apply,LinearMap.sub_apply,LinearMap.zero_apply,
        sub_eq_zero] using ht.symm

lemma stages_annihilate (z w : Module.End F V) {m : ℕ} (_hm : 1≤m)
    (hpur : PureTop z m) (hi : z^m*w*z^m=z^m) (hz : z^(m+1)=0) :
    ∀ k≤m, z^(m+1-k)*stages z w m k=0 := by
  intro k
  induction k with
  | zero => simp [stages,hz]
  | succ k ih =>
    intro hk
    have hkm : k≤m := by omega
    have hd : 1≤m-k := by omega
    have hprev : z^(m-k+1)*stages z w m k=0 := by
      simpa only [show m-k+1=m+1-k by omega] using ih hkm
    have hs := elimination_step z w (stages z w m k) hd (Nat.sub_le m k) hpur hi hprev
    simpa only [stages,show m-(m-k)=k by omega,show m+1-(k+1)=m-k by omega] using hs

lemma stages_on_kernel (z w : Module.End F V) (m : ℕ) {v : V} (hv : z v=0) :
    ∀ k≤m, stages z w m k v=v := by
  intro k
  induction k with
  | zero => simp [stages]
  | succ k ih =>
    intro hk
    have hkm : k≤m := by omega
    have hd : 1≤m-k := by omega
    have hvpow : (z^(m-k)) v=0 := by
      have he : m-k=(m-k-1)+1 := by omega
      rw [he,pow_succ,Module.End.mul_apply,hv,map_zero]
    simp only [stages,Module.End.mul_apply,ih hkm,LinearMap.sub_apply,
      Module.End.one_apply,hvpow,map_zero,sub_zero]

lemma stages_preserve_range (z w : Module.End F V) {m : ℕ} (hz : z^(m+1)=0)
    {v : V} (hv : v∈LinearMap.range z) : ∀ k, stages z w m k v∈LinearMap.range z := by
  intro k
  induction k with
  | zero => simpa [stages] using hv
  | succ k ih =>
    simp only [stages,Module.End.mul_apply,LinearMap.sub_apply,Module.End.one_apply]
    apply Submodule.sub_mem _ ih
    by_cases hk : k=0
    · subst k
      obtain ⟨t,ht⟩ := ih
      have he : (z^m) (stages z w m 0 v)=0 := by
        rw [←ht,←Module.End.mul_apply,←pow_succ,hz,LinearMap.zero_apply]
      have he' : (z^m) v=0 := by simpa only [stages,Module.End.one_apply] using he
      change w ((z^m) v)∈LinearMap.range z
      rw [he',map_zero]
      exact Submodule.zero_mem _
    · refine ⟨(z^(k-1)) (w ((z^(m-k)) (stages z w m k v))),?_⟩
      rw [←Module.End.mul_apply,←pow_succ',show k-1+1=k by omega]

/-- A polynomial in the shared operators, not an objectwise chosen projection. -/
def topProjector {A : Type*} [Ring A] (z w : A) (m : ℕ) : A :=
  (1-z^m*w)*stages z w m m

/-- The constructed projection kills the entire range of z and lands in its kernel. -/
theorem topProjector_annihilates (z w : Module.End F V) {m : ℕ} (hm : 1≤m)
    (hpur : PureTop z m) (hi : z^m*w*z^m=z^m) (hz : z^(m+1)=0) :
    z*topProjector z w m=0 ∧ topProjector z w m*z=0 := by
  have hs : z*stages z w m m=0 := by
    simpa only [show m+1-m=1 by omega,pow_one] using stages_annihilate z w hm hpur hi hz m le_rfl
  have hzu : z*z^m=0 := by rw [←pow_succ',hz]
  constructor
  · calc
      z*topProjector z w m = z*stages z w m m-(z*z^m)*w*stages z w m m := by
        unfold topProjector; noncomm_ring
      _ = 0 := by rw [hs,hzu,zero_mul,zero_mul,sub_zero]
  · ext v
    have hr := stages_preserve_range z w hz (LinearMap.mem_range_self z v) m
    have hk : z (stages z w m m (z v))=0 := congrArg (fun f : Module.End F V => f (z v)) hs
    have ht := top_inverse_on_range hi (hpur _ hk hr)
    simpa only [topProjector,Module.End.mul_apply,LinearMap.sub_apply,
      Module.End.one_apply,LinearMap.zero_apply,sub_eq_zero] using ht.symm

/-- The formula on the kernel is essential to the actual quotient identification. -/
theorem topProjector_on_kernel (z w : Module.End F V) (m : ℕ) {v : V} (hv : z v=0) :
    topProjector z w m v=v-(z^m) (w v) := by
  simp only [topProjector,Module.End.mul_apply,LinearMap.sub_apply,Module.End.one_apply,
    stages_on_kernel z w m hv m le_rfl]

theorem topProjector_idempotent (z w : Module.End F V) {m : ℕ} (hm : 1≤m)
    (hpur : PureTop z m) (hi : z^m*w*z^m=z^m) (hz : z^(m+1)=0) :
    topProjector z w m*topProjector z w m=topProjector z w m := by
  have hp := (topProjector_annihilates z w hm hpur hi hz).1
  have hu : (z^m*w)*(z^m*w)=z^m*w := by rw [←mul_assoc,hi]
  have huP : (z^m*w)*topProjector z w m=0 := by
    calc
      (z^m*w)*topProjector z w m = ((z^m*w)-(z^m*w)*(z^m*w))*stages z w m m := by
        unfold topProjector; noncomm_ring
      _ = 0 := by rw [hu,sub_self,zero_mul]
  ext v
  have hk : z (topProjector z w m v)=0 := congrArg (fun f : Module.End F V => f v) hp
  have hzero : (z^m) (w (topProjector z w m v))=0 :=
    congrArg (fun f : Module.End F V => f v) huP
  change topProjector z w m (topProjector z w m v)=topProjector z w m v
  rw [topProjector_on_kernel z w m hk,hzero,sub_zero]

theorem kernel_residual_in_range (z w : Module.End F V) {m : ℕ} (hm : 1≤m)
    {v : V} (hv : z v=0) : v-topProjector z w m v∈LinearMap.range z := by
  rw [topProjector_on_kernel z w m hv,sub_sub_cancel]
  refine ⟨(z^(m-1)) (w v),?_⟩
  rw [←Module.End.mul_apply,←pow_succ',show m-1+1=m by omega]

section Map
variable {A B : Type*} [Ring A] [Ring B]

theorem map_stages (φ : A →+* B) (z w : A) (m k : ℕ) :
    φ (stages z w m k)=stages (φ z) (φ w) m k := by
  induction k with
  | zero => simp only [stages,map_one]
  | succ k ih => simp only [stages,map_mul,map_sub,map_one,map_pow,ih]

theorem map_topProjector (φ : A →+* B) (z w : A) (m : ℕ) :
    φ (topProjector z w m)=topProjector (φ z) (φ w) m := by
  simp only [topProjector,map_mul,map_sub,map_one,map_pow,map_stages]

/-- Purity is needed only in ONE faithful representation. The resulting identities
are in the acting algebra itself and therefore hold on all its modules. -/
theorem faithful_projector (ρ : A →+* Module.End F V) (hfaith : Function.Injective ρ)
    (z w : A) {m : ℕ} (hm : 1≤m) (hz : z^(m+1)=0)
    (hi : z^m*w*z^m=z^m) (hpur : PureTop (ρ z) m) :
    z*topProjector z w m=0 ∧ topProjector z w m*z=0 ∧
      topProjector z w m*topProjector z w m=topProjector z w m := by
  have hzi : (ρ z)^(m+1)=0 := by simpa only [map_pow,map_zero] using congrArg ρ hz
  have hii : (ρ z)^m*(ρ w)*(ρ z)^m=(ρ z)^m := by
    simpa only [map_pow,map_mul] using congrArg ρ hi
  obtain ⟨hzP,hPz⟩ := topProjector_annihilates (ρ z) (ρ w) hm hpur hii hzi
  have hPP := topProjector_idempotent (ρ z) (ρ w) hm hpur hii hzi
  refine ⟨hfaith ?_,hfaith ?_,hfaith ?_⟩
  · simpa only [map_mul,map_zero,map_topProjector] using hzP
  · simpa only [map_mul,map_zero,map_topProjector] using hPz
  · simpa only [map_mul,map_topProjector] using hPP

/-- Each OTHER representation inherits the quotient projection without an objectwise
purity hypothesis. In particular this includes subobjects,quotients and extensions. -/
theorem all_representation_projection {W : Type*} [AddCommGroup W] [Module F W]
    (ρ : A →+* Module.End F V) (hfaith : Function.Injective ρ)
    (z w : A) {m : ℕ} (hm : 1≤m) (hz : z^(m+1)=0)
    (hi : z^m*w*z^m=z^m) (hpur : PureTop (ρ z) m)
    (τ : A →+* Module.End F W) :
    let P := τ (topProjector z w m)
    τ z*P=0 ∧ P*τ z=0 ∧ P*P=P ∧
      ∀ v, (τ z) v=0 → v-P v∈LinearMap.range (τ z) := by
  obtain ⟨hzP,hPz,hPP⟩ := faithful_projector ρ hfaith z w hm hz hi hpur
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [map_mul,map_zero] using congrArg τ hzP
  · simpa only [map_mul,map_zero] using congrArg τ hPz
  · simpa only [map_mul] using congrArg τ hPP
  · intro v hv
    rw [map_topProjector]
    exact kernel_residual_in_range (τ z) (τ w) hm hv

end Map
end SelfContainedCycle084

