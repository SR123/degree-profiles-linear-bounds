/-
Prompt 05: scalar extension and degree-preserving descent (manuscript `lem:field`).

`K → L` is an arbitrary field extension (`[Algebra K L]`), `σ` an arbitrary variable type,
`Γ ⊆ K[x]` an arbitrary axiom set.  `mapSet Γ ⊆ L[x]` is `Γ` with coefficients mapped to `L`.

Statements proved, with the *same* proof systems as in `PolynomialCalculus`/`Nullstellensatz`:
* `pc_refutes_map_iff`   : degree-`≤ d` ordinary PC refutability is the same over `K` and `L`;
* `pc_derives_map_iff`   : more generally for every `K`-rational line;
* `ns_refutes_map_iff`   : the same for total-product-degree NS;
* equality of the minimum degrees in `ℕ∞` (including `⊤`);
* specialisation to `𝔽_p → L` for ANY field `L` of characteristic `p`, and between two such
  fields.  No embedding into a chosen algebraic closure is used.

METHOD (recorded deviation from the manuscript's proof sketch).  The manuscript argues that
scalar extension commutes with the closure stages (sums, intersections, images) and then uses
Gaussian elimination.  Here the descent is proved directly on derivations: for every
`K`-linear functional `λ : L → K`, applying `λ` coefficientwise is `K`-linear, commutes with
multiplication by `K`-rational polynomials, does not raise degrees, and turns an `L`-scalar
multiple into another functional image (`λ (c ·)`).  Hence the set of `L`-polynomials all of
whose functional images are `K`-derivable is an `L`-subspace closed under the PC rules.
The *statement* of `lem:field` is unchanged; the stage-by-stage identity
`V_j(L) = L ⊗ V_j(K)` is NOT formalised (it is not needed for the lemma).
-/
import DegreeProfilesReview.Nullstellensatz
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod

open MvPolynomial

namespace DegreeProfilesReview.FieldDescent

open DegreeProfilesReview.PC DegreeProfilesReview.NS

variable {σ : Type*} {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Coefficient extension `K[x] → L[x]`. -/
noncomputable abbrev ext : MvPolynomial σ K →+* MvPolynomial σ L := map (algebraMap K L)

/-- The axiom set with coefficients mapped to `L`. -/
def mapSet (L : Type*) [Field L] [Algebra K L] (Γ : Set (MvPolynomial σ K)) :
    Set (MvPolynomial σ L) :=
  (fun f => map (algebraMap K L) f) '' Γ

/-! ### Coefficientwise functionals -/

/-- Apply a `K`-linear functional `λ : L → K` to every coefficient. -/
noncomputable def coeffwise (lam : L →ₗ[K] K) : MvPolynomial σ L →ₗ[K] MvPolynomial σ K :=
  Finsupp.mapRange.linearMap lam

theorem coeff_coeffwise (lam : L →ₗ[K] K) (P : MvPolynomial σ L) (m : σ →₀ ℕ) :
    coeff m (coeffwise lam P) = lam (coeff m P) := rfl

/-- Support containment gives a degree inequality, across coefficient rings. -/
theorem totalDegree_le_of_support_subset' {R S : Type*} [CommSemiring R] [CommSemiring S]
    {p : MvPolynomial σ R} {q : MvPolynomial σ S} (h : p.support ⊆ q.support) :
    p.totalDegree ≤ q.totalDegree :=
  Finset.sup_mono h

/-- (a) On `K`-rational polynomials `λ` acts as the scalar `λ 1`. -/
theorem coeffwise_map (lam : L →ₗ[K] K) (f : MvPolynomial σ K) :
    coeffwise lam (map (algebraMap K L) f) = lam 1 • f := by
  apply MvPolynomial.ext
  intro m
  rw [coeff_coeffwise, coeff_map, coeff_smul, Algebra.algebraMap_eq_smul_one, map_smul,
    smul_eq_mul, smul_eq_mul, mul_comm]

/-- (e) `λ` commutes with multiplication by a `K`-rational polynomial. -/
theorem coeffwise_mul_map (lam : L →ₗ[K] K) (P : MvPolynomial σ L) (f : MvPolynomial σ K) :
    coeffwise lam (P * map (algebraMap K L) f) = coeffwise lam P * f := by
  classical
  apply MvPolynomial.ext
  intro m
  rw [coeff_coeffwise, coeff_mul, coeff_mul, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [coeff_coeffwise, coeff_map, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one,
    map_smul, smul_eq_mul, mul_comm]

/-- (b) `λ` commutes with multiplication by a variable. -/
theorem coeffwise_X_mul (lam : L →ₗ[K] K) (i : σ) (P : MvPolynomial σ L) :
    coeffwise lam (X i * P) = X i * coeffwise lam P := by
  have := coeffwise_mul_map lam P (X i : MvPolynomial σ K)
  rw [map_X] at this
  rw [mul_comm, this, mul_comm]

/-- (c) An `L`-scalar is absorbed into the functional. -/
theorem coeffwise_smul (lam : L →ₗ[K] K) (c : L) (P : MvPolynomial σ L) :
    coeffwise lam (c • P) = coeffwise (lam.comp (LinearMap.mulLeft K c)) P := by
  apply MvPolynomial.ext
  intro m
  rw [coeff_coeffwise, coeff_coeffwise, coeff_smul]
  rfl

/-- (d) `λ` does not raise the total degree. -/
theorem totalDegree_coeffwise_le (lam : L →ₗ[K] K) (P : MvPolynomial σ L) :
    (coeffwise lam P).totalDegree ≤ P.totalDegree := by
  apply totalDegree_le_of_support_subset'
  intro m hm
  rw [MvPolynomial.mem_support_iff, coeff_coeffwise] at hm
  rw [MvPolynomial.mem_support_iff]
  intro h0
  apply hm
  rw [h0, map_zero]

/-- A `K`-linear retraction `L → K` of the inclusion. -/
theorem exists_retraction (K L : Type*) [Field K] [Field L] [Algebra K L] :
    ∃ lam : L →ₗ[K] K, lam 1 = 1 := by
  have hker : LinearMap.ker (Algebra.linearMap K L) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (algebraMap K L).injective
  obtain ⟨g, hg⟩ := (Algebra.linearMap K L).exists_leftInverse_of_injective hker
  refine ⟨g, ?_⟩
  have := LinearMap.congr_fun hg 1
  rw [LinearMap.comp_apply, Algebra.linearMap_apply, (algebraMap K L).map_one,
    LinearMap.id_apply] at this
  exact this

/-- Extension of coefficients preserves the total degree exactly. -/
theorem totalDegree_map_eq (f : MvPolynomial σ K) :
    (map (algebraMap K L) f).totalDegree = f.totalDegree := by
  apply le_antisymm
  · exact totalDegree_le_of_support_subset' (support_map_subset _ f)
  · obtain ⟨lam, hlam⟩ := exists_retraction K L
    have h1 := totalDegree_coeffwise_le lam (map (algebraMap K L) f)
    rw [coeffwise_map, hlam, one_smul] at h1
    exact h1

/-! ### PC: ascent -/

theorem map_mem_span_of_mem_span {l : List (MvPolynomial σ K)} {f : MvPolynomial σ K}
    (hf : f ∈ Submodule.span K {g | g ∈ l}) :
    map (algebraMap K L) f ∈
      Submodule.span L {g | g ∈ l.map (fun f => map (algebraMap K L) f)} := by
  induction hf using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (List.mem_map_of_mem hx)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hx

theorem IsProof.map {Γ : Set (MvPolynomial σ K)} {l : List (MvPolynomial σ K)}
    (hp : IsProof Γ l) :
    IsProof (mapSet L Γ) (l.map (fun f => MvPolynomial.map (algebraMap K L) f)) := by
  induction hp with
  | nil => exact IsProof.nil
  | ax _ hf ih => exact IsProof.ax ih ⟨_, hf, rfl⟩
  | lin _ hf ih => exact IsProof.lin ih (map_mem_span_of_mem_span hf)
  | @mulX l g i _ hg ih =>
    have : MvPolynomial.map (algebraMap K L) (X i * g) =
        X i * MvPolynomial.map (algebraMap K L) g := by rw [map_mul, map_X]
    rw [List.map_cons, this]
    exact IsProof.mulX i ih (List.mem_map_of_mem hg)

/-- Mapping a `K`-derivation into `L` (the easy direction). -/
theorem derives_map {Γ : Set (MvPolynomial σ K)} {d : ℕ} {f : MvPolynomial σ K}
    (h : Derives Γ d f) : Derives (mapSet L Γ) d (map (algebraMap K L) f) := by
  obtain ⟨l, hp, hb, hm⟩ := h
  refine ⟨_, IsProof.map hp, ?_, List.mem_map_of_mem hm⟩
  intro g hg
  obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
  rw [totalDegree_map_eq]
  exact hb g₀ hg₀

/-! ### PC: descent -/

theorem derivable_X_mul {Γ : Set (MvPolynomial σ K)} {d : ℕ} (i : σ) {g : MvPolynomial σ K}
    (hg : g ∈ derivable Γ d) (hdeg : (X i * g).totalDegree ≤ d) : X i * g ∈ derivable Γ d := by
  obtain ⟨l, hp, hb, hm⟩ := hg
  exact ⟨X i * g :: l, IsProof.mulX i hp hm, DegBounded.cons hdeg hb, by simp⟩

/-- The `L`-subspace of `L`-polynomials all of whose functional images are `K`-derivable. -/
def descended (L : Type*) [Field L] [Algebra K L] (Γ : Set (MvPolynomial σ K)) (d : ℕ) :
    Submodule L (MvPolynomial σ L) where
  carrier := {P | ∀ lam : L →ₗ[K] K, coeffwise lam P ∈ derivable Γ d}
  zero_mem' := by
    intro lam
    rw [map_zero]
    exact Submodule.zero_mem _
  add_mem' := by
    intro P Q hP hQ lam
    rw [map_add]
    exact Submodule.add_mem _ (hP lam) (hQ lam)
  smul_mem' := by
    intro c P hP lam
    show coeffwise lam (c • P) ∈ derivable Γ d
    rw [coeffwise_smul]
    exact hP _

theorem IsProof.mem_descended {Γ : Set (MvPolynomial σ K)} {d : ℕ}
    {l : List (MvPolynomial σ L)} (hp : IsProof (mapSet L Γ) l) (hb : DegBounded d l) :
    ∀ g ∈ l, g ∈ descended L Γ d := by
  induction hp with
  | nil => intro g hg; cases hg
  | @ax l F _ hF ih =>
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg'
    · obtain ⟨f, hf, rfl⟩ := hF
      intro lam
      rw [coeffwise_map]
      apply Submodule.smul_mem
      have hdeg : f.totalDegree ≤ d := by
        rw [← totalDegree_map_eq (L := L)]
        exact hb _ (by simp)
      refine ⟨[f], IsProof.ax IsProof.nil hf, ?_, by simp⟩
      intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      exact hdeg
    · exact ih (fun g hg => hb g (List.mem_cons_of_mem _ hg)) g hg'
  | @lin l F _ hF ih =>
    have ih' := ih (fun g hg => hb g (List.mem_cons_of_mem _ hg))
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg'
    · exact (Submodule.span_le.mpr (fun g hg => ih' g hg)) hF
    · exact ih' g hg'
  | @mulX l g₀ i _ hg₀ ih =>
    have ih' := ih (fun g hg => hb g (List.mem_cons_of_mem _ hg))
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg'
    · intro lam
      rw [coeffwise_X_mul]
      apply derivable_X_mul i (ih' g₀ hg₀ lam)
      rw [← coeffwise_X_mul]
      exact le_trans (totalDegree_coeffwise_le lam _) (hb _ (by simp))
    · exact ih' g hg'

/-- **PC field descent for every `K`-rational line.** -/
theorem pc_derives_map_iff {Γ : Set (MvPolynomial σ K)} {d : ℕ} {f : MvPolynomial σ K} :
    Derives (mapSet L Γ) d (map (algebraMap K L) f) ↔ Derives Γ d f := by
  constructor
  · rintro ⟨l, hp, hb, hm⟩
    obtain ⟨lam, hlam⟩ := exists_retraction K L
    have := IsProof.mem_descended hp hb _ hm lam
    rwa [coeffwise_map, hlam, one_smul] at this
  · exact derives_map

/-- **PC part of `lem:field`.** -/
theorem pc_refutes_map_iff {Γ : Set (MvPolynomial σ K)} {d : ℕ} :
    Refutes (mapSet L Γ) d ↔ Refutes Γ d := by
  unfold Refutes
  rw [← pc_derives_map_iff (L := L) (f := (1 : MvPolynomial σ K)), map_one]

theorem pcDegree_map (Γ : Set (MvPolynomial σ K)) : pcDegree (mapSet L Γ) = pcDegree Γ :=
  enat_eq_of_forall_le_iff fun d => by
    rw [pcDegree_le_iff, pcDegree_le_iff, pc_refutes_map_iff]

/-! ### NS: ascent and descent through the certificate span -/

theorem NSspan_map {Γ : Set (MvPolynomial σ K)} {d : ℕ} {g : MvPolynomial σ K}
    (hg : g ∈ NSspan Γ d) : map (algebraMap K L) g ∈ NSspan (mapSet L Γ) d := by
  unfold NSspan at hg
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, f, hf, hdeg, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨m, map (algebraMap K L) f, ⟨f, hf, rfl⟩, ?_, ?_⟩
    · rw [totalDegree_map_eq]; exact hdeg
    · rw [map_mul, map_monomial, (algebraMap K L).map_one]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hx

/-- The `L`-subspace of polynomials all of whose functional images lie in the `K`-certificate
span. -/
def descendedNS (L : Type*) [Field L] [Algebra K L] (Γ : Set (MvPolynomial σ K)) (d : ℕ) :
    Submodule L (MvPolynomial σ L) where
  carrier := {P | ∀ lam : L →ₗ[K] K, coeffwise lam P ∈ NSspan Γ d}
  zero_mem' := by
    intro lam
    rw [map_zero]
    exact Submodule.zero_mem _
  add_mem' := by
    intro P Q hP hQ lam
    rw [map_add]
    exact Submodule.add_mem _ (hP lam) (hQ lam)
  smul_mem' := by
    intro c P hP lam
    show coeffwise lam (c • P) ∈ NSspan Γ d
    rw [coeffwise_smul]
    exact hP _

theorem NSspan_le_descendedNS (Γ : Set (MvPolynomial σ K)) (d : ℕ) :
    NSspan (mapSet L Γ) d ≤ descendedNS L Γ d := by
  apply Submodule.span_le.mpr
  rintro _ ⟨m, F, ⟨f, hf, rfl⟩, hdeg, rfl⟩
  intro lam
  have hmon : (monomial m (1 : L)) = map (algebraMap K L) (monomial m (1 : K)) := by
    rw [map_monomial, (algebraMap K L).map_one]
  rw [hmon, ← map_mul, coeffwise_map]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  refine ⟨m, f, hf, ?_, rfl⟩
  rw [totalDegree_map_eq] at hdeg
  exact hdeg

/-- **NS part of `lem:field`.** -/
theorem ns_refutes_map_iff {Γ : Set (MvPolynomial σ K)} {d : ℕ} :
    NSRefutes (mapSet L Γ) d ↔ NSRefutes Γ d := by
  rw [nsRefutes_iff_one_mem_NSspan, nsRefutes_iff_one_mem_NSspan]
  constructor
  · intro h
    obtain ⟨lam, hlam⟩ := exists_retraction K L
    have := NSspan_le_descendedNS Γ d h lam
    have h1 : (1 : MvPolynomial σ L) = map (algebraMap K L) (1 : MvPolynomial σ K) := by
      rw [map_one]
    rwa [h1, coeffwise_map, hlam, one_smul] at this
  · intro h
    have := NSspan_map (L := L) h
    rwa [map_one] at this

theorem nsDegree_map (Γ : Set (MvPolynomial σ K)) : nsDegree (mapSet L Γ) = nsDegree Γ :=
  enat_eq_of_forall_le_iff fun d => by
    rw [nsDegree_le_iff, nsDegree_le_iff, ns_refutes_map_iff]

/-! ### Specialisation to prime-field coefficients -/

section PrimeField

variable (p : ℕ) [Fact p.Prime]

/-- For coefficients in `𝔽_p`, the PC and NS degrees over ANY field `L` of characteristic `p`
equal the degrees over `𝔽_p`.  The statement is about these prime-field coefficients only. -/
theorem degrees_over_char_p_field (L : Type*) [Field L] [CharP L p]
    (Γ : Set (MvPolynomial σ (ZMod p))) :
    letI := ZMod.algebra L p
    pcDegree (mapSet L Γ) = pcDegree Γ ∧ nsDegree (mapSet L Γ) = nsDegree Γ := by
  letI := ZMod.algebra L p
  exact ⟨pcDegree_map Γ, nsDegree_map Γ⟩

/-- Two fields of characteristic `p` give the same degrees; neither needs to embed in the
other or in a chosen algebraic closure. -/
theorem degrees_between_char_p_fields (L L' : Type*) [Field L] [CharP L p] [Field L']
    [CharP L' p] (Γ : Set (MvPolynomial σ (ZMod p))) :
    letI := ZMod.algebra L p
    letI := ZMod.algebra L' p
    pcDegree (mapSet L Γ) = pcDegree (mapSet L' Γ) ∧
      nsDegree (mapSet L Γ) = nsDegree (mapSet L' Γ) := by
  letI := ZMod.algebra L p
  letI := ZMod.algebra L' p
  exact ⟨(pcDegree_map Γ).trans (pcDegree_map Γ).symm,
    (nsDegree_map Γ).trans (nsDegree_map Γ).symm⟩

end PrimeField

end DegreeProfilesReview.FieldDescent
