import MarkedLeaf

namespace SelfContainedCycle058
open SelfContainedCycle035 SelfContainedCycle036 SelfContainedCycle037 SelfContainedCycle038
open SelfContainedCycle040 SelfContainedCycle046 SelfContainedCycle052 SelfContainedCycle053 SelfContainedCycle054
open SelfContainedCycle055 SelfContainedCycle057
open MvPolynomial DegreeProfilesReview.NS DegreeProfilesReview.PC

/-- Finite linear assembly in the actual unnormalized design space. -/
theorem design_sum {F ι : Type*} [CommRing F] {n m d : ℕ} (A : Finset ι) (φ : ι → Edges → F)
    (h : ∀ i∈A,IsDesign n m d (φ i)) : IsDesign n m d (fun P => ∑ i∈A,φ i P) := by
  have hs := (designSpace F n m d).sum_mem h
  change IsDesign n m d (∑ i∈A,φ i) at hs
  have he : (∑ i∈A,φ i)=(fun P => ∑ i∈A,φ i P) := by
    ext P; simp only [Finset.sum_apply]
  exact he ▸ hs

/-- An explicit extension: interpolate the old terminal values using actual square coordinates. -/
noncomputable def extendDesign {F : Type*} [CommRing F] (n m D : ℕ) (ψ : Edges → F) : Edges → F :=
  fun P => ∑ T ∈ (terminalFamily n m).filter (fun T => T.card≤D-1),
    ψ T * (squareLeafCoeff m P T:F)

theorem extendDesign_isDesign {F : Type*} [CommRing F] {p a n m D : ℕ}
    (hp : p.Prime) [CharP F p] (hn : 2*D≤n) (hdq : D < p^a) (hnm : n≤m)
    (hdiv : p^a∣m-n) (ψ : Edges → F) : IsDesign n m D (extendDesign n m D ψ) := by
  classical
  apply design_sum
  intro T hT
  have ht := squareLeaf_rectangular_design (F:=F) hp hn hdq hnm hdiv T (Finset.mem_filter.mp hT).1
  simpa only [Pi.smul_apply,smul_eq_mul] using design_smul (ψ T) ht

/-- All old terminal coordinates are preserved, with their original labels. -/
theorem extendDesign_terminal {F : Type*} [CommRing F] (n m D : ℕ) (ψ : Edges → F)
    (P : Edges) (hP : P∈terminalFamily n m) (hd : P.card≤D-1) :
    extendDesign n m D ψ P=ψ P := by
  classical
  have h := (mem_terminalFamily _ _ _).mp hP
  unfold extendDesign
  simp_rw [squareLeafCoeff_terminal P _ h.2.1 h.2.2]
  simp [hP,hd]

/-- The degree-extension premise from the ordinary-PC invariant is now discharged. -/
theorem rectangular_design_extension {F : Type*} [CommRing F] {p a n m D : ℕ}
    (hp : p.Prime) [CharP F p] (hn : 2*D≤n) (hdq : D < p^a) (hnm : n≤m)
    (hdiv : p^a∣m-n) (ψ : Edges → F) (hψ : IsDesign n m (D-1) ψ) :
    IsDesign n m D (extendDesign n m D ψ) ∧
      ∀ P,P⊆grid n m → P.card≤D-1 → extendDesign n m D ψ P=ψ P := by
  have hν := extendDesign_isDesign hp hn hdq hnm hdiv ψ
  refine ⟨hν,?_⟩
  intro P hP hd
  exact design_determined_by_terminals (design_mono hν (Nat.sub_le _ _)) hψ
    (fun T hT hdT => extendDesign_terminal n m D ψ T hT hdT) P hP hd

/-- Ordinary PC in the original polynomial ring, with extension supplied by the construction. -/
theorem no_PCRefutes_rectangle {F : Type*} [Field F] {p a n m D : ℕ}
    (hp : p.Prime) [CharP F p] (hn : 1≤n) (hsize : 2*D≤n) (hdq : D < p^a)
    (hnm : n≤m) (hdiv : p^a∣m-n) :
    ¬ Refutes {f : MvPolynomial (Var n m) F | IsBAxiom n m f} D := by
  apply no_PCRefutes_of_extension hn (hn.trans hnm) ?_
    (actual_rectangular_design hp hsize hdq hnm hdiv)
  intro ψ hψ
  obtain ⟨hν,hagree⟩ := rectangular_design_extension hp hsize hdq hnm hdiv ψ hψ
  exact ⟨extendDesign n m D ψ,hν,fun P _ hP hd => hagree P hP hd⟩

/-- The characteristic-two concrete family has ordinary-PC degree at least q=n/3. -/
theorem concrete_family_PC_lower_bound {F : Type*} [Field F] [CharP F 2] (a d : ℕ)
    (hd : d < 2^a) :
    ¬ Refutes {f : MvPolynomial (Var (3*2^a) (6*2^a)) F | IsBAxiom (3*2^a) (6*2^a) f} d := by
  have hq : 0 < 2^a := pow_pos (by decide) _
  apply no_PCRefutes_rectangle (p:=2) (a:=a) (by decide) (by omega) (by omega) hd (by omega)
  have he : 6*2^a-3*2^a=3*2^a := by omega
  rw [he]
  exact dvd_mul_left _ _

/-- Every actual PC refutation has degree at least q; a=0 is included. -/
theorem concrete_family_PC_refutation_degree {F : Type*} [Field F] [CharP F 2] (a d : ℕ)
    (h : Refutes {f : MvPolynomial (Var (3*2^a) (6*2^a)) F | IsBAxiom (3*2^a) (6*2^a) f} d) :
    2^a≤d := Nat.le_of_not_gt (fun hd => concrete_family_PC_lower_bound a d hd h)

/-- Both original proof systems have the concrete linear lower bound. -/
theorem concrete_family_both_lower_bounds {F : Type*} [Field F] [CharP F 2] (a d : ℕ)
    (hd : d < 2^a) :
    (¬ NSRefutes {f : MvPolynomial (Var (3*2^a) (6*2^a)) F | IsBAxiom (3*2^a) (6*2^a) f} d) ∧
    (¬ Refutes {f : MvPolynomial (Var (3*2^a) (6*2^a)) F | IsBAxiom (3*2^a) (6*2^a) f} d) :=
  ⟨concrete_family_NS_lower_bound a d hd,concrete_family_PC_lower_bound a d hd⟩


/-- Non-vacuity: an actual nonempty terminal coordinate is a nonzero unnormalized design. -/
theorem nonempty_terminal_coordinate_example :
    IsDesign 4 8 2 (fun P => (squareLeafCoeff 8 P {(2,2)}:ZMod 2)) ∧
    (squareLeafCoeff 8 ∅ {(2,2)}:ZMod 2)=0 ∧
    (squareLeafCoeff 8 {(2,2)} {(2,2)}:ZMod 2)=1 := by
  refine ⟨?_,?_,?_⟩
  · apply squareLeaf_rectangular_design (p:=2) (a:=2) (by decide) (by decide)
      (by decide) (by decide) (by decide)
    exact (mem_terminalFamily _ _ _).mpr ⟨by decide,by decide,positive_terminal_example⟩
  · rw [squareLeafCoeff_terminal _ _ (by simp [IsMatching]) empty_terminal]
    norm_num
  · rw [squareLeafCoeff_terminal _ _ (by decide) positive_terminal_example]
    norm_num

/-- Proper rectangles in characteristics two and three, plus the exponent-zero boundary. -/
theorem concrete_PC_boundary_examples :
    (¬ Refutes {f : MvPolynomial (Var 4 8) (ZMod 2) | IsBAxiom 4 8 f} 2) ∧
    (¬ Refutes {f : MvPolynomial (Var 4 7) (ZMod 3) | IsBAxiom 4 7 f} 2) ∧
    (¬ Refutes {f : MvPolynomial (Var 3 6) (ZMod 2) | IsBAxiom 3 6 f} 0) := by
  refine ⟨?_,?_,?_⟩
  · exact no_PCRefutes_rectangle (p:=2) (a:=2) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · exact no_PCRefutes_rectangle (p:=3) (a:=1) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · exact concrete_family_PC_lower_bound 0 0 (by decide)

end SelfContainedCycle058
