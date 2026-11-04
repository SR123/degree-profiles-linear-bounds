/-
Stage 3, step 5: a NARROWING of the Stage 2 input M5, and the Stage 2 pipeline re-derived from
the narrower input.

Why.  Stage 2's `M5` asks the ambient deletion functor `Φhat` to be MONOIDAL.  That is true
for "restrict to `S_n × A`, then semisimplify `A`", whose target is a tensor category that is
not a category of representations.  It is FALSE for the elementary functor that the source
also allows and that Stage 3 constructs,

      `V ↦ image of (V^A → V_A)`      (the unit component of the semisimplification),

which is only lax monoidal.  What the proof of Stage 2 actually uses is much less:

  (κ)  for every permutation module `K[𝒰_N]` of support `≤ r` and EVERY object `Y`, a natural
       isomorphism   `Φhat (K[𝒰_N] ⊗ Y) ≅ J (K[𝒰_n]) ⊗ Φhat Y`,
       compatible with the product identifications.

`M5w` records exactly this.  It is implied by `M5` (`M5.toM5w`), so nothing proved in Stage 2
is lost, and it holds for both functors.

* `M5w.tens_Φ_spec`  — `Φ` carries `X ⊗ S ⟶ X ⊗ L` at rank `N` to the one at rank `n`;
* `Template.ΦCompatW`, `pc_stepW`, `ns_stepW`;
* `DeletionInterfaceW`, `DeletionHypothesisW`, and the endpoint
  `uniform_template_linear_bounds_w`.
-/
import DegreeProfilesReview.TemplatePeriodicity

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace DegreeProfilesReview.Deletion

open DegreeProfilesReview.Uniform DegreeProfilesReview.MonoidalCompat

/-- **M5, narrowed.**  As `M5`, except that `Φhat` is a plain functor equipped with a natural
isomorphism `κ` commuting it past tensoring with a bounded permutation module. -/
structure M5w {K : Type} [Field K] {r N n : ℕ}
    {BN : Type u₂} [Category.{v₂} BN] [Abelian BN] {Bn : Type u₂} [Category.{v₂} Bn] [Abelian Bn]
    (PN : M4.{v₂, v₃, u₂, u₃} K r N BN) (Pn : M4.{v₂, v₃, u₂, u₃} K r n Bn) (Φ : BN ⥤ Bn) where
  𝒯 : Type u₄
  [cat𝒯 : Category.{v₄} 𝒯]
  [mon𝒯 : MonoidalCategory 𝒯]
  J : Pn.R ⥤ 𝒯
  [J_monoidal : J.Monoidal]
  [J_full : J.Full]
  [J_faithful : J.Faithful]
  Φhat : PN.R ⥤ 𝒯
  γ : PN.ι ⋙ Φhat ≅ Φ ⋙ Pn.ι ⋙ J
  δ : ∀ (𝒰 : BasisSystem) (h : 𝒰.Bounded r), Φ.obj (PN.perm 𝒰 h) ≅ Pn.perm 𝒰 h
  δ_mat : ∀ {𝒰 𝒱 : BasisSystem} (hU : 𝒰.Bounded r) (hV : 𝒱.Bounded r) (a : InvMatrix K 𝒰 𝒱),
    Φ.map (PN.mat hU hV a) ≫ (δ 𝒱 hV).hom = (δ 𝒰 hU).hom ≫ Pn.mat hU hV a
  κ : ∀ {𝒰 : BasisSystem} (hU : 𝒰.Bounded r) (Y : PN.R),
    Φhat.obj (PN.ι.obj (PN.perm 𝒰 hU) ⊗ Y) ≅ J.obj (Pn.ι.obj (Pn.perm 𝒰 hU)) ⊗ Φhat.obj Y
  κ_nat : ∀ {𝒰 : BasisSystem} (hU : 𝒰.Bounded r) {Y Y' : PN.R} (f : Y ⟶ Y'),
    Φhat.map (PN.ι.obj (PN.perm 𝒰 hU) ◁ f) ≫ (κ hU Y').hom =
      (κ hU Y).hom ≫ (J.obj (Pn.ι.obj (Pn.perm 𝒰 hU)) ◁ Φhat.map f)
  δ_prod : ∀ {𝒰 𝒱 : BasisSystem} (hU : 𝒰.Bounded r) (hV : 𝒱.Bounded r)
    (hUV : (𝒰.prod 𝒱).Bounded r),
    Φhat.map (PN.prodIso hU hV hUV).hom ≫ γ.hom.app (PN.perm (𝒰.prod 𝒱) hUV) ≫
        J.map (Pn.ι.map (δ (𝒰.prod 𝒱) hUV).hom) =
      (κ hU (PN.ι.obj (PN.perm 𝒱 hV))).hom ≫
        (J.obj (Pn.ι.obj (Pn.perm 𝒰 hU)) ◁
          (γ.hom.app (PN.perm 𝒱 hV) ≫ J.map (Pn.ι.map (δ 𝒱 hV).hom))) ≫
        Functor.LaxMonoidal.μ J (Pn.ι.obj (Pn.perm 𝒰 hU)) (Pn.ι.obj (Pn.perm 𝒱 hV)) ≫
        J.map (Pn.prodIso hU hV hUV).hom

attribute [instance] M5w.cat𝒯 M5w.mon𝒯 M5w.J_monoidal M5w.J_full M5w.J_faithful

section

variable {K : Type} [Field K] {r N n : ℕ}
  {BN : Type u₂} [Category.{v₂} BN] [Abelian BN] {Bn : Type u₂} [Category.{v₂} Bn] [Abelian Bn]
  {PN : M4.{v₂, v₃, u₂, u₃} K r N BN} {Pn : M4.{v₂, v₃, u₂, u₃} K r n Bn} {Φ : BN ⥤ Bn}

/-- The Stage 2 input implies the narrowed input. -/
noncomputable def M5.toM5w (m5 : M5.{v₂, v₃, v₄, u₂, u₃, u₄} PN Pn Φ) :
    M5w.{v₂, v₃, v₄, u₂, u₃, u₄} PN Pn Φ where
  𝒯 := m5.𝒯
  J := m5.J
  Φhat := m5.Φhat
  γ := m5.γ
  δ := m5.δ
  δ_mat := m5.δ_mat
  κ := fun {𝒰} hU Y =>
    (Functor.Monoidal.μIso m5.Φhat _ Y).symm ≪≫ whiskerRightIso (m5.α 𝒰 hU) (m5.Φhat.obj Y)
  κ_nat := fun {𝒰} hU {Y Y'} f => by
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.Monoidal.μIso_inv, whiskerRightIso_hom,
      Category.assoc]
    rw [← Functor.OplaxMonoidal.δ_natural_right_assoc, whisker_exchange]
  δ_prod := fun {𝒰 𝒱} hU hV hUV => by
    have h := m5.δ_prod hU hV hUV
    rw [h, tensorComparison_hom]
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.Monoidal.μIso_inv, whiskerRightIso_hom,
      Category.assoc, Iso.app_hom, Functor.mapIso_hom]
    rw [tensorHom_def]
    simp only [Category.assoc, M5.α, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]

namespace M5w

variable (m5 : M5w.{v₂, v₃, v₄, u₂, u₃, u₄} PN Pn Φ)

theorem γ_nat {A A' : BN} (f : A ⟶ A') :
    m5.Φhat.map (PN.ι.map f) ≫ m5.γ.hom.app A' =
      m5.γ.hom.app A ≫ m5.J.map (Pn.ι.map (Φ.map f)) :=
  m5.γ.hom.naturality f

/-- **`Φ` is compatible with `X ⊗ S ⟶ X ⊗ L`**, from the narrowed input. -/
theorem tens_Φ_spec {𝒰 𝒱 : BasisSystem} (hU : 𝒰.Bounded r) (hV : 𝒱.Bounded r)
    (hUV : (𝒰.prod 𝒱).Bounded r) {S : BN} (s : S ⟶ PN.perm 𝒱 hV) [Mono s]
    {S' : Bn} (s' : S' ⟶ Pn.perm 𝒱 hV) [Mono s'] (e : Φ.obj S ≅ S')
    (hs : Φ.map s ≫ (m5.δ 𝒱 hV).hom = e.hom ≫ s') :
    ∃ eT : Φ.obj (PN.sub hU hV hUV s) ≅ Pn.sub hU hV hUV s',
      Φ.map (PN.tens hU hV hUV s) ≫ (m5.δ (𝒰.prod 𝒱) hUV).hom =
        eT.hom ≫ Pn.tens hU hV hUV s' := by
  let aS : m5.Φhat.obj (PN.ι.obj S) ≅ m5.J.obj (Pn.ι.obj S') :=
    m5.γ.app S ≪≫ m5.J.mapIso (Pn.ι.mapIso e)
  let θ : m5.J.obj (Pn.ι.obj (Φ.obj (PN.sub hU hV hUV s))) ≅
      m5.J.obj (Pn.ι.obj (Pn.sub hU hV hUV s')) :=
    (m5.γ.app (PN.sub hU hV hUV s)).symm ≪≫ m5.Φhat.mapIso (PN.subIso hU hV hUV s) ≪≫
      m5.κ hU (PN.ι.obj S) ≪≫ whiskerLeftIso _ aS ≪≫ Functor.Monoidal.μIso m5.J _ _ ≪≫
      m5.J.mapIso (Pn.subIso hU hV hUV s').symm
  refine ⟨Pn.ι.preimageIso (m5.J.preimageIso θ), ?_⟩
  apply Pn.ι.map_injective
  apply m5.J.map_injective
  -- the square for `s` in the ambient target
  have hsq : m5.Φhat.map (PN.ι.map s) ≫
      (m5.γ.hom.app (PN.perm 𝒱 hV) ≫ m5.J.map (Pn.ι.map (m5.δ 𝒱 hV).hom)) =
      aS.hom ≫ m5.J.map (Pn.ι.map s') := by
    simp only [aS, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
    rw [← Category.assoc, m5.γ_nat, Category.assoc, ← Functor.map_comp, ← Functor.map_comp, hs,
      Functor.map_comp, Functor.map_comp, Category.assoc]
  have hw : m5.Φhat.map (PN.ι.obj (PN.perm 𝒰 hU) ◁ PN.ι.map s) ≫
      (m5.κ hU (PN.ι.obj (PN.perm 𝒱 hV))).hom ≫
      (m5.J.obj (Pn.ι.obj (Pn.perm 𝒰 hU)) ◁
        (m5.γ.hom.app (PN.perm 𝒱 hV) ≫ m5.J.map (Pn.ι.map (m5.δ 𝒱 hV).hom))) =
      (m5.κ hU (PN.ι.obj S)).hom ≫ (m5.J.obj (Pn.ι.obj (Pn.perm 𝒰 hU)) ◁ aS.hom) ≫
        (m5.J.obj (Pn.ι.obj (Pn.perm 𝒰 hU)) ◁ m5.J.map (Pn.ι.map s')) := by
    rw [← Category.assoc, m5.κ_nat, Category.assoc, ← MonoidalCategory.whiskerLeft_comp, hsq,
      MonoidalCategory.whiskerLeft_comp]
  have hprod := m5.δ_prod hU hV hUV
  have hL : m5.J.map (Pn.ι.map (Φ.map (PN.tens hU hV hUV s) ≫ (m5.δ (𝒰.prod 𝒱) hUV).hom)) =
      m5.γ.inv.app _ ≫ m5.Φhat.map (PN.subIso hU hV hUV s).hom ≫
        (m5.κ hU (PN.ι.obj S)).hom ≫ (m5.J.obj (Pn.ι.obj (Pn.perm 𝒰 hU)) ◁ aS.hom) ≫
        Functor.LaxMonoidal.μ m5.J _ _ ≫
        m5.J.map (Pn.ι.obj (Pn.perm 𝒰 hU) ◁ Pn.ι.map s') ≫
        m5.J.map (Pn.prodIso hU hV hUV).hom := by
    rw [Functor.map_comp, Functor.map_comp]
    have h1 : m5.J.map (Pn.ι.map (Φ.map (PN.tens hU hV hUV s))) =
        m5.γ.inv.app _ ≫ m5.Φhat.map (PN.ι.map (PN.tens hU hV hUV s)) ≫ m5.γ.hom.app _ := by
      rw [m5.γ_nat, Iso.inv_hom_id_app_assoc]
    rw [h1, PN.ι_tens, Functor.map_comp, Functor.map_comp]
    simp only [Category.assoc]
    congr 2
    rw [hprod, reassoc_of% hw, Functor.LaxMonoidal.μ_natural_right_assoc]
  rw [hL, Functor.map_comp, Functor.map_comp, Pn.ι_tens]
  simp only [Functor.preimageIso_hom, Functor.map_preimage, θ, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_inv, Functor.map_comp, Category.assoc,
    Functor.Monoidal.μIso_hom, whiskerLeftIso_hom]
  congr 5
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]

end M5w

end

/-- The five inputs with the narrowed M5. -/
structure DeletionInterfaceW (K : Type) [Field K] (p q r n : ℕ) where
  m1 : M1.{v₁, u₁} q r n
  m2 : M2.{v₁, v₂, u₁, u₂} p m1
  m3 : M3 m2
  m4N : M4.{v₂, v₃, u₂, u₃} K r (n + q) m2.BN
  m4n : M4.{v₂, v₃, u₂, u₃} K r n m2.Bn
  m5 : M5w.{v₂, v₃, v₄, u₂, u₃, u₄} m4N m4n m3.Φ

/-- A Stage 2 interface is in particular a narrowed interface. -/
noncomputable def DeletionInterface.toW {K : Type} [Field K] {p q r n : ℕ}
    (I : DeletionInterface.{v₁, v₂, v₃, v₄, u₁, u₂, u₃, u₄} K p q r n) :
    DeletionInterfaceW.{v₁, v₂, v₃, v₄, u₁, u₂, u₃, u₄} K p q r n :=
  ⟨I.m1, I.m2, I.m3, I.m4N, I.m4n, I.m5.toM5w⟩

end DegreeProfilesReview.Deletion

namespace DegreeProfilesReview.Uniform

open DegreeProfilesReview.Deletion DegreeProfilesReview.Transport DegreeProfilesReview.Profiles

namespace Template

variable {K : Type} [Field K] (T : Template K) {d : ℕ} (hd : 1 ≤ d) {N n : ℕ}
  {BN : Type u₂} [Category.{v₂} BN] [Abelian BN] {Bn : Type u₂} [Category.{v₂} Bn] [Abelian Bn]
  {PN : M4.{v₂, v₃, u₂, u₃} K (T.k * d + T.s) N BN}
  {Pn : M4.{v₂, v₃, u₂, u₃} K (T.k * d + T.s) n Bn} {Φ : BN ⥤ Bn}

/-- `Φ` carries the rank-`N` datum to the rank-`n` datum, from the narrowed input. -/
noncomputable def ΦCompatW (m5 : M5w.{v₂, v₃, v₄, u₂, u₃, u₄} PN Pn Φ) :
    PCCompat Φ (T.catDatum hd PN) (T.catDatum hd Pn) where
  αW := m5.δ _ _
  αL := m5.δ _ _
  αM := m5.δ _ _
  αU := m5.δ _ _
  αV₀ := m5.δ _ _
  hℓ := m5.δ_mat _ _ _
  hμ := m5.δ_mat _ _ _
  hv₀ := m5.δ_mat _ _ _
  hc := m5.δ_mat _ _ _
  hT := fun {_} s _ {_} s' _ e hs =>
    m5.tens_Φ_spec (T.var_bounded' d hd) (T.low_bounded d) (T.mul_bounded d hd) s s' e hs

end Template

namespace Template

variable {K : Type} [Field K] (T : Template K)

/-- One deletion step for ordinary PC, from the narrowed interface. -/
theorem pc_stepW {p q n d : ℕ} (hp : 2 ≤ p) (hd : 1 ≤ d) (hn0 : T.n0 ≤ n)
    (hn : 2 * (T.k * d + T.s) < n)
    (I : DeletionInterfaceW.{v₁, v₂, v₃, v₄, u₁, u₂, u₃, u₄} K p q (T.k * d + T.s) n) :
    PC.Refutes (T.inst (n + q)) d ↔ PC.Refutes (T.inst n) d := by
  haveI : I.m3.Φ.IsEquivalence := I.m3.isEquivalence hp hn
  rw [PC.refutes_iff_one_mem_Vinf, PC.refutes_iff_one_mem_Vinf, PC.mem_Vinf_iff,
    PC.mem_Vinf_iff]
  apply exists_congr
  intro j
  rw [← T.pc_stage_iff hd I.m4N (le_trans hn0 (Nat.le_add_right n q)) j,
    ← T.pc_stage_iff hd I.m4n hn0 j]
  exact const_mem_iff I.m3.Φ (T.ΦCompatW hd I.m5) j

/-- One deletion step for NS, from the narrowed interface. -/
theorem ns_stepW {p q n d : ℕ} (hp : 2 ≤ p) (hn0 : T.n0 ≤ n)
    (hn : 2 * (T.k * d + T.s) < n)
    (I : DeletionInterfaceW.{v₁, v₂, v₃, v₄, u₁, u₂, u₃, u₄} K p q (T.k * d + T.s) n) :
    NS.NSRefutes (T.inst (n + q)) d ↔ NS.NSRefutes (T.inst n) d := by
  haveI : I.m3.Φ.IsEquivalence := I.m3.isEquivalence hp hn
  rw [NS.nsRefutes_iff_one_mem_NSspan, NS.nsRefutes_iff_one_mem_NSspan,
    ← T.ns_iff I.m4N (le_trans hn0 (Nat.le_add_right n q)), ← T.ns_iff I.m4n hn0]
  exact image_membership_iff I.m3.Φ _ _ _ _ (I.m5.δ _ _) (I.m5.δ _ _) (I.m5.δ _ _)
    (I.m5.δ_mat _ _ _) (I.m5.δ_mat _ _ _)

end Template

/-- The narrowed representation-theoretic hypothesis, in the strict range. -/
def DeletionHypothesisW (K : Type) [Field K] (p k s n0 : ℕ) : Prop :=
  ∀ d a n : ℕ, 1 ≤ d → k * d + s < p ^ a → n0 ≤ n → 2 * (k * d + s) < n →
    Nonempty (DeletionInterfaceW.{v₁, v₂, v₃, v₄, u₁, u₂, u₃, u₄} K p (p ^ a) (k * d + s) n)

theorem DeletionHypothesis.toW {K : Type} [Field K] {p k s n0 : ℕ}
    (H : DeletionHypothesis.{v₁, v₂, v₃, v₄, u₁, u₂, u₃, u₄} K p k s n0) :
    DeletionHypothesisW.{v₁, v₂, v₃, v₄, u₁, u₂, u₃, u₄} K p k s n0 :=
  fun d a n hd ha hn0 hn => (H d a n hd ha hn0 hn).map DeletionInterface.toW

section Periodicity

variable {R : Type} [Field R] (T : Template R) {p : ℕ} (hp : 2 ≤ p)
  (K : Type) [Field K] [Algebra R K]

include hp in
theorem thresholdPeriodic_pc_w
    (H : DeletionHypothesisW.{v₁, v₂, v₃, v₄, u₁, u₂, u₃, u₄} K p T.k T.s T.n0) :
    ThresholdPeriodic p T.k T.s T.n0 T.pcProfile := by
  intro d hd a ha n m hn hm h2n h2m hc
  rw [← T.pcProfile_map (K := K) n, ← T.pcProfile_map (K := K) m]
  unfold Template.pcProfile
  rw [PC.pcDegree_le_iff, PC.pcDegree_le_iff]
  refine congr_of_step (Pr := fun n => PC.Refutes ((T.map (algebraMap R K)).inst n) d)
    (B := max T.n0 (2 * (T.k * d + T.s) + 1)) (q := p ^ a) ?_
    (max_le hn h2n) (max_le hm h2m) hc
  intro n' hn'
  have h1 : T.n0 ≤ n' := le_trans (le_max_left _ _) hn'
  have h2 : 2 * (T.k * d + T.s) < n' := le_trans (le_max_right _ _) hn'
  obtain ⟨I⟩ := H d a n' hd ha h1 h2
  exact (T.map (algebraMap R K)).pc_stepW hp hd h1 h2 I

include hp in
theorem thresholdPeriodic_ns_w
    (H : DeletionHypothesisW.{v₁, v₂, v₃, v₄, u₁, u₂, u₃, u₄} K p T.k T.s T.n0) :
    ThresholdPeriodic p T.k T.s T.n0 T.nsProfile := by
  intro d hd a ha n m hn hm h2n h2m hc
  rw [← T.nsProfile_map (K := K) n, ← T.nsProfile_map (K := K) m]
  unfold Template.nsProfile
  rw [NS.nsDegree_le_iff, NS.nsDegree_le_iff]
  refine congr_of_step (Pr := fun n => NS.NSRefutes ((T.map (algebraMap R K)).inst n) d)
    (B := max T.n0 (2 * (T.k * d + T.s) + 1)) (q := p ^ a) ?_
    (max_le hn h2n) (max_le hm h2m) hc
  intro n' hn'
  have h1 : T.n0 ≤ n' := le_trans (le_max_left _ _) hn'
  have h2 : 2 * (T.k * d + T.s) < n' := le_trans (le_max_right _ _) hn'
  obtain ⟨I⟩ := H d a n' hd ha h1 h2
  exact (T.map (algebraMap R K)).ns_stepW hp h1 h2 I

end Periodicity

/-- **Endpoint, from the narrowed hypothesis.**  Same conclusion as the Stage 2 endpoint. -/
theorem uniform_template_linear_bounds_w {R : Type} [Field R] (T : Template R) {p : ℕ}
    (hp : 2 ≤ p) (K : Type) [Field K] [Algebra R K]
    (H : DeletionHypothesisW.{v₁, v₂, v₃, v₄, u₁, u₂, u₃, u₄} K p T.k T.s T.n0) :
    LinearBoundsFor p T.k T.s T.n0 (fun n => PC.pcDegree (T.inst n)) ∧
    LinearBoundsFor p T.k T.s T.n0 (fun n => NS.nsDegree (T.inst n)) ∧
    (∀ n, PC.pcDegree (T.inst n) ≤ NS.nsDegree (T.inst n)) ∧
    (IsT4 (fun n => PC.pcDegree (T.inst n)) (onset T.k T.s T.n0) → ∀ B : ℕ,
      ∃ n d : ℕ, B ≤ n ∧ B ≤ d ∧ PC.pcDegree (T.inst n) = (d : ℕ∞) ∧
        (d : ℕ∞) ≤ NS.nsDegree (T.inst n) ∧
        (n : ℚ) / ((p + 2) * T.k) - T.s / T.k ≤ d) := by
  have Ppc : PeriodicProfile T.pcProfile (onset T.k T.s T.n0) (period p T.k T.s) :=
    template_periodicProfile hp T.hk T.hn0 (thresholdPeriodic_pc_w T hp K H) T.zeroStable_pc
  have Pns : PeriodicProfile T.nsProfile (onset T.k T.s T.n0) (period p T.k T.s) :=
    template_periodicProfile hp T.hk T.hn0 (thresholdPeriodic_ns_w T hp K H) T.zeroStable_ns
  exact ⟨linearBoundsFor_of_periodic hp T.hk Ppc, linearBoundsFor_of_periodic hp T.hk Pns,
    T.pcProfile_le_nsProfile,
    fun h4 B => simultaneous_peaks hp T.hk Ppc h4 T.pcProfile_le_nsProfile B⟩

end DegreeProfilesReview.Uniform
