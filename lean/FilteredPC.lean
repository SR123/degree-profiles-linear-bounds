import PigeonholeRestriction

namespace SelfContainedCycle080
open MvPolynomial DegreeProfilesReview.PC DegreeProfilesReview.NS SelfContainedCycle072
variable {F σ τ : Type*} [Field F]

theorem proof_mono {Γ Δ : Set (MvPolynomial σ F)} (h : Γ⊆Δ)
    {l} (hl : IsProof Γ l) : IsProof Δ l := by
  induction hl with
  | nil => exact IsProof.nil
  | ax _ hf ih => exact IsProof.ax ih (h hf)
  | lin _ hf ih => exact IsProof.lin ih hf
  | mulX i _ hg ih => exact IsProof.mulX i ih hg

/-- Only axioms of degree at most D can be used in an actual degree-D PC proof. -/
theorem proof_filter {Γ : Set (MvPolynomial σ F)} {l D}
    (hl : IsProof Γ l) (hb : DegBounded D l) :
    IsProof {f | f∈Γ ∧ f.totalDegree≤D} l := by
  induction hl with
  | nil => exact IsProof.nil
  | @ax l f _ hf ih =>
    exact IsProof.ax (ih (fun g hg => hb g (List.mem_cons_of_mem _ hg)))
      ⟨hf,hb f (by simp)⟩
  | @lin l f _ hf ih =>
    exact IsProof.lin (ih (fun g hg => hb g (List.mem_cons_of_mem _ hg))) hf
  | @mulX l g i _ hg ih =>
    exact IsProof.mulX i (ih (fun f hf => hb f (List.mem_cons_of_mem _ hf))) hg

theorem refutes_filter_iff {Γ : Set (MvPolynomial σ F)} {D} :
    Refutes Γ D ↔ Refutes {f | f∈Γ ∧ f.totalDegree≤D} D := by
  constructor
  · rintro ⟨l,hp,hb,hm⟩
    exact ⟨l,proof_filter hp hb,hb,hm⟩
  · rintro ⟨l,hp,hb,hm⟩
    exact ⟨l,proof_mono (fun _ h => h.1) hp,hb,hm⟩

/-- Unlike unrestricted substitution, only images of USABLE inputs need checking. -/
theorem refutes_filtered_substitution (φ : MvPolynomial σ F →ₐ[F] MvPolynomial τ F)
    (hX : ∀ i,(∃ c,φ (X i)=C c) ∨ ∃ j,φ (X i)=X j)
    {Γ : Set (MvPolynomial σ F)} {Δ : Set (MvPolynomial τ F)} {D}
    (hΓ : ∀ f∈Γ,f.totalDegree≤D → φ f=0 ∨ φ f∈Δ)
    (h : Refutes Γ D) : Refutes Δ D :=
  refutes_substitution φ hX (fun f hf => hΓ f hf.1 hf.2) (refutes_filter_iff.mp h)

/-- A common root of just the usable inputs excludes actual ordinary PC. -/
theorem no_refutes_low_root {Γ : Set (MvPolynomial σ F)} {D} (α : σ → F)
    (hΓ : ∀ f∈Γ,f.totalDegree≤D → aeval α f=0) : ¬Refutes Γ D := by
  rintro ⟨l,hp,hb,hm⟩
  have hi : ∀ f∈l,aeval α f=0 := by
    clear hm
    induction hp with
    | nil => simp
    | @ax l f _ hf ih =>
      have ht := ih (fun g hg => hb g (List.mem_cons_of_mem _ hg))
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact hΓ g hf (hb g (by simp))
      · exact ht g hg
    | @lin l f _ hf ih =>
      have ht := ih (fun g hg => hb g (List.mem_cons_of_mem _ hg))
      have hs : Submodule.span F {g | g∈l} ≤ LinearMap.ker (aeval α).toLinearMap :=
        Submodule.span_le.mpr (fun g hg => ht g hg)
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact hs hf
      · exact ht g hg
    | @mulX l g i _ hg ih =>
      have ht := ih (fun f hf => hb f (List.mem_cons_of_mem _ hf))
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · rw [map_mul,ht g hg,mul_zero]
      · exact ht f hf
  simpa using hi 1 hm

/-- Convenient derived rules retain the original list-based PC definition. -/
theorem derives_ax {Γ : Set (MvPolynomial σ F)} {D} {f : MvPolynomial σ F}
    (hf : f∈Γ) (hd : f.totalDegree≤D) : Derives Γ D f := by
  refine ⟨[f],IsProof.ax IsProof.nil hf,?_,by simp⟩
  intro g hg
  rcases List.mem_singleton.mp hg with rfl
  exact hd

theorem derives_mulX {Γ : Set (MvPolynomial σ F)} {D} {f : MvPolynomial σ F}
    (hf : Derives Γ D f) (i : σ) (hd : (X i*f).totalDegree≤D) :
    Derives Γ D (X i*f) := by
  obtain ⟨l,hp,hb,hm⟩ := hf
  exact ⟨X i*f::l,IsProof.mulX i hp hm,DegBounded.cons hd hb,by simp⟩

theorem derives_sub {Γ : Set (MvPolynomial σ F)} {D} {f g : MvPolynomial σ F}
    (hf : Derives Γ D f) (hg : Derives Γ D g) : Derives Γ D (f-g) :=
  (derivable Γ D).sub_mem hf hg

theorem derives_add {Γ : Set (MvPolynomial σ F)} {D} {f g : MvPolynomial σ F}
    (hf : Derives Γ D f) (hg : Derives Γ D g) : Derives Γ D (f+g) :=
  (derivable Γ D).add_mem hf hg

/-- Replacing each usable input by a bounded derivation preserves actual PC degree. -/
theorem refutes_of_derived_inputs {Γ Δ : Set (MvPolynomial σ F)} {D}
    (hΓ : ∀ f∈Γ,f.totalDegree≤D → Derives Δ D f) (href : Refutes Γ D) : Refutes Δ D := by
  obtain ⟨l,hp,hb,hm⟩ := href
  have hi : ∀ f∈l,Derives Δ D f := by
    clear hm
    induction hp with
    | nil => simp
    | @ax l f _ hf ih =>
      have ht := ih (fun g hg => hb g (List.mem_cons_of_mem _ hg))
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact hΓ g hf (hb g (by simp))
      · exact ht g hg
    | @lin l f _ hf ih =>
      have ht := ih (fun g hg => hb g (List.mem_cons_of_mem _ hg))
      have hs : Submodule.span F {g | g∈l} ≤ derivable Δ D :=
        Submodule.span_le.mpr (fun g hg => ht g hg)
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact hs hf
      · exact ht g hg
    | @mulX l g i _ hg ih =>
      have ht := ih (fun f hf => hb f (List.mem_cons_of_mem _ hf))
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact derives_mulX (ht g hg) i (hb _ (by simp))
      · exact ht f hf
  exact hi 1 hm

end SelfContainedCycle080
