import FilteredPC

namespace SelfContainedCycle081
open MvPolynomial DegreeProfilesReview.PC DegreeProfilesReview.NS SelfContainedCycle080
variable {F σ : Type*} [Field F]

/-- Input replacement for an arbitrary derived polynomial, retaining actual PC lists. -/
theorem derives_of_derived_inputs {Γ Δ : Set (MvPolynomial σ F)} {D}
    (hΓ : ∀ f∈Γ, f.totalDegree≤D → Derives Δ D f)
    {f : MvPolynomial σ F} (href : Derives Γ D f) : Derives Δ D f := by
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
  exact hi f hm

/-- Multiplication by a polynomial is simulated with the actual total-degree budget. -/
theorem derives_mul {Γ : Set (MvPolynomial σ F)} {D} {f g : MvPolynomial σ F}
    (hg : Derives Γ D g) (hd : f.totalDegree+g.totalDegree≤D) :
    Derives Γ D (f*g) := by
  have hm : Derives ({g} : Set (MvPolynomial σ F)) D (f*g) :=
    Vinf_le_derivable _ _ (NSspan_le_Vinf _ _ (mul_mem_NSspan (by simp) hd))
  exact derives_of_derived_inputs (by intro a ha _; simpa using (Set.mem_singleton_iff.mp ha) ▸ hg) hm

/-- Lift every line of a proof by a fixed polynomial; multiplication steps commute. -/
theorem derives_guard_lift {Γ Δ : Set (MvPolynomial σ F)} {d}
    (c : MvPolynomial σ F) (hΓ : ∀ f∈Γ,c*f∈Δ)
    {f : MvPolynomial σ F} (hf : Derives Γ d f) :
    Derives Δ (d+c.totalDegree) (c*f) := by
  obtain ⟨l,hp,hb,hm⟩ := hf
  let L : MvPolynomial σ F →ₗ[F] MvPolynomial σ F :=
    { toFun := fun g => c*g
      map_add' := fun _ _ => mul_add _ _ _
      map_smul' := fun _ _ => mul_smul_comm _ _ _ }
  have hi : ∀ g∈l,Derives Δ (d+c.totalDegree) (c*g) := by
    clear hm
    induction hp with
    | nil => simp
    | @ax l g _ hg ih =>
      have ht := ih (fun a ha => hb a (List.mem_cons_of_mem _ ha))
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · apply derives_ax (hΓ a hg)
        have h := totalDegree_mul c a
        have h' := hb a (by simp)
        omega
      · exact ht a ha
    | @lin l g _ hg ih =>
      have ht := ih (fun a ha => hb a (List.mem_cons_of_mem _ ha))
      have hs : Submodule.span F {a | a∈l} ≤ (derivable Δ (d+c.totalDegree)).comap L :=
        Submodule.span_le.mpr (fun a ha => ht a ha)
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hs hg
      · exact ht a ha
    | @mulX l g i _ hg ih =>
      have ht := ih (fun a ha => hb a (List.mem_cons_of_mem _ ha))
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · have heq : X i*(c*g)=c*(X i*g) := by ring
        rw [← heq]
        apply derives_mulX (ht g hg)
        rw [heq]
        have h := totalDegree_mul c (X i*g)
        have h' := hb (X i*g) (by simp)
        omega
      · exact ht a ha
  exact hi f hm

/-- All inputs are guarded; this is not the partially guarded manuscript encoding. -/
def fullGuard (z : σ) (A B : Set (MvPolynomial σ F)) : Set (MvPolynomial σ F) :=
  (fun f => X z*f) '' A ∪ (fun g => (1-X z)*g) '' B ∪ {X z^2-X z}

theorem fullGuard_left (z : σ) (A B : Set (MvPolynomial σ F)) {f} (hf : f∈A) :
    X z*f∈fullGuard z A B := Or.inl (Or.inl ⟨f,hf,rfl⟩)

theorem fullGuard_right (z : σ) (A B : Set (MvPolynomial σ F)) {g} (hg : g∈B) :
    (1-X z)*g∈fullGuard z A B := Or.inl (Or.inr ⟨g,hg,rfl⟩)

theorem left_guard_derived {z : σ} {A B : Set (MvPolynomial σ F)} {d}
    (h : Refutes A d) : Derives (fullGuard z A B) (d+1) (X z) := by
  have h' := derives_guard_lift (X z) (fun f hf => fullGuard_left z A B hf) h
  simpa using h'

theorem right_guard_derived {z : σ} {A B : Set (MvPolynomial σ F)} {d}
    (h : Refutes B d) : Derives (fullGuard z A B) (d+1) (1-X z) := by
  have h' := derives_guard_lift (1-X z) (fun g hg => fullGuard_right z A B hg) h
  have hd : (1-X z : MvPolynomial σ F).totalDegree≤1 :=
    (totalDegree_sub _ _).trans (by simp)
  simpa using h'.mono (by omega : d+(1-X z : MvPolynomial σ F).totalDegree≤d+1)

theorem fullGuard_refutes_succ {z : σ} {A B : Set (MvPolynomial σ F)} {d}
    (hA : Refutes A d) (hB : Refutes B d) : Refutes (fullGuard z A B) (d+1) := by
  change Derives _ _ 1
  convert derives_add (left_guard_derived (B:=B) hA) (right_guard_derived (A:=A) hB) using 1
  · ring

/-- If B refutes one degree earlier, recover every usable A input without extra cost. -/
theorem fullGuard_high_low {z : σ} {A B : Set (MvPolynomial σ F)} {d}
    (hA : Refutes A (d+1)) (hB : Refutes B d)
    (hdeg : ∀ f∈A,f.totalDegree≤d) : Refutes (fullGuard z A B) (d+1) := by
  have hz := right_guard_derived (A:=A) (z:=z) hB
  apply refutes_of_derived_inputs (Γ:=A) (D:=d+1) _ hA
  intro f hf _
  have hzf : Derives (fullGuard z A B) (d+1) (X z*f) :=
    derives_ax (fullGuard_left z A B hf) (by
      have h := totalDegree_mul (X z : MvPolynomial σ F) f
      have h' := hdeg f hf
      simp only [totalDegree_X] at h
      omega)
  have hfz := derives_mul (f:=f) hz (by
    have h := (totalDegree_sub (1 : MvPolynomial σ F) (X z)).trans (by simp : max (1 : MvPolynomial σ F).totalDegree (X z).totalDegree≤1)
    have h' := hdeg f hf
    omega)
  convert derives_add hzf hfz using 1
  · ring

theorem fullGuard_low_high {z : σ} {A B : Set (MvPolynomial σ F)} {d}
    (hA : Refutes A d) (hB : Refutes B (d+1))
    (hdeg : ∀ g∈B,g.totalDegree≤d) : Refutes (fullGuard z A B) (d+1) := by
  have hz := left_guard_derived (B:=B) (z:=z) hA
  apply refutes_of_derived_inputs (Γ:=B) (D:=d+1) _ hB
  intro g hg _
  have hzg : Derives (fullGuard z A B) (d+1) ((1-X z)*g) :=
    derives_ax (fullGuard_right z A B hg) (by
      have h := totalDegree_mul (1-X z : MvPolynomial σ F) g
      have h' := hdeg g hg
      have hs := (totalDegree_sub (1 : MvPolynomial σ F) (X z)).trans (by simp : max (1 : MvPolynomial σ F).totalDegree (X z).totalDegree≤1)
      omega)
  have hgz := derives_mul (f:=g) hz (by simpa using Nat.add_le_add_right (hdeg g hg) 1)
  convert derives_add hzg hgz using 1
  · ring

end SelfContainedCycle081
