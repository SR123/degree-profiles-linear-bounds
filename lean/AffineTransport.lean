import PigeonholeRestriction

namespace SelfContainedCycle074
open MvPolynomial SelfContainedCycle054 SelfContainedCycle058 SelfContainedCycle072
open DegreeProfilesReview.PC DegreeProfilesReview.NS
variable {F σ τ : Type*} [Field F]

/-- Multiplication by an affine polynomial is simulated by actual PC rules. -/
theorem derives_affine_mul [Fintype τ] {Δ : Set (MvPolynomial τ F)} {D : ℕ}
    {g : MvPolynomial τ F} (hg : Derives Δ D g) (hd : g.totalDegree+1≤D)
    (c : F) (a : τ → F) :
    Derives Δ D ((C c + ∑ j, a j • X j)*g) := by
  classical
  have hx (j : τ) : X j*g ∈ derivable Δ D := by
    obtain ⟨l,hp,hb,hm⟩ := hg
    refine ⟨X j*g::l,IsProof.mulX j hp hm,DegBounded.cons ?_ hb,by simp⟩
    exact (totalDegree_mul _ _).trans (by simpa [totalDegree_X,add_comm] using hd)
  rw [add_mul,Finset.sum_mul,← smul_eq_C_mul]
  apply (derivable Δ D).add_mem ((derivable Δ D).smul_mem c hg)
  apply Submodule.sum_mem
  intro j _
  simpa only [smul_mul_assoc] using (derivable Δ D).smul_mem (a j) (hx j)

/-- Actual PC refutations survive affine substitution with bounded axiom derivations.
    No image/intersection or exactness hypothesis is hidden in the statement. -/
theorem affine_refutes [Fintype τ]
    (φ : MvPolynomial σ F →ₐ[F] MvPolynomial τ F)
    (hX : ∀ i, ∃ (c : F) (a : τ → F), φ (X i)=C c+∑ j, a j • X j)
    {Γ : Set (MvPolynomial σ F)} {Δ : Set (MvPolynomial τ F)} {e d : ℕ}
    (hΓ : ∀ f∈Γ, Derives Δ e (φ f)) (href : Refutes Γ d) :
    Refutes Δ (max e d) := by
  classical
  have hdX (i : σ) : (φ (X i)).totalDegree≤1 := by
    obtain ⟨c,a,he⟩ := hX i
    rw [he]
    apply (totalDegree_add _ _).trans
    apply max_le (by simp)
    apply (totalDegree_finset_sum _ _).trans
    exact Finset.sup_le (fun j _ => (totalDegree_smul_le _ _).trans (by simp))
  obtain ⟨l,hp,hb,hm⟩ := href
  have hh : ∀ g∈l, Derives Δ (max e d) (φ g) := by
    clear hm
    induction hp with
    | nil => intro g hg; cases hg
    | @ax l f _ hf ih =>
      have hi := ih (fun g hg => hb g (List.mem_cons_of_mem _ hg))
      intro g hg
      rcases List.mem_cons.mp hg with rfl | ht
      · exact (hΓ _ hf).mono (le_max_left _ _)
      · exact hi _ ht
    | @lin l f _ hf ih =>
      have hi := ih (fun g hg => hb g (List.mem_cons_of_mem _ hg))
      intro g hg
      rcases List.mem_cons.mp hg with rfl | ht
      · have hle : Submodule.span F {g | g∈l} ≤
            (derivable Δ (max e d)).comap φ.toLinearMap :=
          Submodule.span_le.mpr (fun g hg => hi g hg)
        exact hle hf
      · exact hi _ ht
    | @mulX l g i _ hg ih =>
      have hi := ih (fun g hg => hb g (List.mem_cons_of_mem _ hg))
      intro f hf
      rcases List.mem_cons.mp hf with rfl | ht
      · by_cases hz : g=0
        · simp only [hz,mul_zero,map_zero]
          exact (derivable Δ (max e d)).zero_mem
        · have hdeg := (totalDegree_succ_le_X_mul i hz).trans (hb _ (by simp))
          have hsub := degree_substitution φ hdX g
          obtain ⟨c,a,he⟩ := hX i
          rw [map_mul,he]
          exact derives_affine_mul (hi g hg) (by omega) c a
      · exact hi _ ht
  simpa only [map_one] using hh _ hm

/-- The identities needed for filling unused column capacity. -/
theorem slack_times_entry {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] (x : ι → R) (i : ι) :
    (1-∑ j, x j)*x i = -(x i^2-x i) - ∑ j∈Finset.univ.erase i, x j*x i := by
  classical
  have hs := Finset.sum_erase_add Finset.univ x (Finset.mem_univ i)
  rw [← hs,sub_mul,add_mul,Finset.sum_mul]
  ring

theorem slack_boolean {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] (x : ι → R) :
    (1-∑ i, x i)^2-(1-∑ i, x i) =
      ∑ i, (x i^2-x i) + ∑ i, ∑ j∈Finset.univ.erase i, x j*x i := by
  classical
  have h (i : ι) := slack_times_entry x i
  have he : (1-∑ i,x i)*(∑ i,x i) =
      -(∑ i,(x i^2-x i)) - ∑ i,∑ j∈Finset.univ.erase i,x j*x i := by
    rw [Finset.mul_sum]
    simp_rw [h]
    rw [Finset.sum_sub_distrib,Finset.sum_neg_distrib]
  calc (1-∑ i,x i)^2-(1-∑ i,x i) = -((1-∑ i,x i)*(∑ i,x i)) := by ring
       _ = _ := by rw [he]; ring
end SelfContainedCycle074
