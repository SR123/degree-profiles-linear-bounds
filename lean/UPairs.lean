/-
Claude, 27 Sep 2026.  Undecidability, part K3: all six type pairs and all disjoint type sets
(manuscript `thm:undecidable`, strong form).

Fix a prime `p` and a field `K` of characteristic `p`.  Inputs are normalized sentences (coded by
Mathlib's `Primcodable`); the promise `Promised φ` is: well formed and no model of any size
`n ≥ 1`.  For type sets `A, B` a *separator* is a partial computable `D : Sentence →. Bool` that
halts with `true` on every promised input whose type lies in `A` and halts with `false` on every
promised input whose type lies in `B`; nothing is required elsewhere (it may diverge).  Total
computable separators are a special case (`typeSep_of_computable`).

* `undecidable_pair_NS/PC`: for all distinct `a, b ∈ {1, 2, 3, 4}` there is no separator of
  `{a}` and `{b}`.
* `undecidable_disjoint_NS/PC`: for all nonempty disjoint `A, B ⊆ {1, 2, 3, 4}` there is no
  separator of `A` and `B`.
* `pairs_iff_disjoint`: for any type assignment, the six-pair statement and the disjoint-set
  statement are equivalent; `typeSep_symm`: separating `{a}` from `{b}` is equivalent to
  separating `{b}` from `{a}`, so the ordered pairs reduce to six unordered ones.
* `undecidable_union_NS_via_pairs`: the every-union theorem of part H1 recovered as the case
  `B = {1,2,3,4} \ A` (`union_of_sep`).

Proof.  Witness order `T1 ≺ T4 ≺ T3 ≺ T2` (`wrank`).  For `a ≺ b` the reduction is
`c ↦ ψ_a ∨_* (ψ_b ∧ θ_{U(c)})`.  If `U(c)` halts, the second block is eventually bounded and the
join has type `a` (`iType_sandwich`).  If not, the second block has the profile of `ψ_b` at every
`n ≥ 1` and the join is sandwiched between `max (ψ_a, ψ_b)` and that `+ 1`: for `a = 1` it has
type `b` (`iType_sandwich`), for `b = 2` type T2 (`iType2_mono`), and for `(a, b) = (4, 3)` type
T3 (`iType3_of`: `B̂` has degree at most `5` and `ψ_3` degree at most `p` off the multiples of `p`,
while on them `ψ_3` has the profile of `η`).
-/
import UUndecidable
import UJoinDeg
import UJoinComputable
import UProfiles

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ClaudeUndec
open Nat.Partrec DegreeProfilesReview.NS DegreeProfilesReview.Profiles

/-! ### Separators -/

/-- A separator of the type sets `A` and `B` for the type assignment `T` on the promise class:
a partial computable `D` that halts with output `true` on every promised input whose type lies in
`A`, and halts with output `false` on every promised input whose type lies in `B`.  Nothing is
required elsewhere; `D` may diverge or answer arbitrarily outside the promise. -/
def TypeSep (T : Sentence → ℕ → Prop) (A B : Set ℕ) : Prop :=
  ∃ D : Sentence →. Bool, Partrec D ∧
    (∀ φ, Promised φ → ∀ τ ∈ A, T φ τ → true ∈ D φ) ∧
    (∀ φ, Promised φ → ∀ τ ∈ B, T φ τ → false ∈ D φ)

/-- A total computable separator is in particular a separator. -/
theorem typeSep_of_computable (T : Sentence → ℕ → Prop) (A B : Set ℕ) (D : Sentence → Bool)
    (hD : Computable D) (h1 : ∀ φ, Promised φ → ∀ τ ∈ A, T φ τ → D φ = true)
    (h2 : ∀ φ, Promised φ → ∀ τ ∈ B, T φ τ → D φ = false) : TypeSep T A B :=
  ⟨fun φ => Part.some (D φ), hD.partrec,
    fun φ hφ τ hτ ht => by show true ∈ Part.some (D φ); rw [h1 φ hφ τ hτ ht]; exact Part.mem_some _,
    fun φ hφ τ hτ ht => by show false ∈ Part.some (D φ); rw [h2 φ hφ τ hτ ht]; exact Part.mem_some _⟩

theorem typeSep_symm (T : Sentence → ℕ → Prop) (A B : Set ℕ) : TypeSep T A B ↔ TypeSep T B A := by
  constructor <;>
  · rintro ⟨D, hD, h1, h2⟩
    refine ⟨fun φ => (D φ).map (fun b => !b),
      hD.map ((Primrec.not.to_comp).comp Computable.snd).to₂, fun φ hφ τ hτ ht => ?_,
      fun φ hφ τ hτ ht => ?_⟩
    · exact (Part.mem_map_iff _).mpr ⟨false, h2 φ hφ τ hτ ht, rfl⟩
    · exact (Part.mem_map_iff _).mpr ⟨true, h1 φ hφ τ hτ ht, rfl⟩

theorem typeSep_mono (T : Sentence → ℕ → Prop) {A B A' B' : Set ℕ} (hA : A' ⊆ A) (hB : B' ⊆ B)
    (h : TypeSep T A B) : TypeSep T A' B' := by
  obtain ⟨D, hD, h1, h2⟩ := h
  exact ⟨D, hD, fun φ hφ τ hτ => h1 φ hφ τ (hA hτ), fun φ hφ τ hτ => h2 φ hφ τ (hB hτ)⟩

/-- A separator composed with a computable reduction into the promise class, sending `P` to
`A`-types and `¬ P` to `B`-types, decides `P`.  (The composite halts everywhere, so it is a total
computable function by `Partrec.of_eq_tot`.) -/
theorem sep_decides {α : Type} [Primcodable α] {T : Sentence → ℕ → Prop} {A B : Set ℕ}
    {D : Sentence →. Bool} (hD : Partrec D) (h1 : ∀ φ, Promised φ → ∀ τ ∈ A, T φ τ → true ∈ D φ)
    (h2 : ∀ φ, Promised φ → ∀ τ ∈ B, T φ τ → false ∈ D φ) (f : α → Sentence) (hf : Computable f)
    (hprom : ∀ c, Promised (f c)) (P : α → Prop) (hyes : ∀ c, P c → ∃ τ ∈ A, T (f c) τ)
    (hno : ∀ c, ¬ P c → ∃ τ ∈ B, T (f c) τ) : ComputablePred P := by
  classical
  have hdom : ∀ c, (D (f c)).Dom := fun c => by
    by_cases hc : P c
    · obtain ⟨τ, hτ, ht⟩ := hyes c hc
      exact Part.dom_iff_mem.mpr ⟨_, h1 _ (hprom c) τ hτ ht⟩
    · obtain ⟨τ, hτ, ht⟩ := hno c hc
      exact Part.dom_iff_mem.mpr ⟨_, h2 _ (hprom c) τ hτ ht⟩
  have hg : Computable fun c => (D (f c)).get (hdom c) :=
    Partrec.of_eq_tot (hD.comp hf) (fun c => Part.get_mem _)
  refine ComputablePred.computable_iff.mpr ⟨_, hg, funext fun c => propext ⟨fun hc => ?_, fun hgc => ?_⟩⟩
  · obtain ⟨τ, hτ, ht⟩ := hyes c hc
    exact Part.mem_unique (Part.get_mem _) (h1 _ (hprom c) τ hτ ht)
  · by_contra hc
    obtain ⟨τ, hτ, ht⟩ := hno c hc
    have := Part.mem_unique (Part.get_mem (hdom c)) (h2 _ (hprom c) τ hτ ht)
    rw [this] at hgc
    exact Bool.false_ne_true hgc

/-- **Six pairs ⟺ all disjoint sets**, for any type assignment. -/
theorem pairs_iff_disjoint (T : Sentence → ℕ → Prop) (S : Set ℕ) :
    (∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬ TypeSep T {a} {b}) ↔
      (∀ A B : Set ℕ, A ⊆ S → B ⊆ S → A.Nonempty → B.Nonempty → Disjoint A B →
        ¬ TypeSep T A B) := by
  constructor
  · intro h A B hA hB ⟨a, ha⟩ ⟨b, hb⟩ hdisj hsep
    have hab : a ≠ b := fun e => Set.disjoint_left.mp hdisj ha (e ▸ hb)
    exact h a (hA ha) b (hB hb) hab
      (typeSep_mono T (Set.singleton_subset_iff.mpr ha) (Set.singleton_subset_iff.mpr hb) hsep)
  · intro h a ha b hb hab
    exact h {a} {b} (Set.singleton_subset_iff.mpr ha) (Set.singleton_subset_iff.mpr hb)
      (Set.singleton_nonempty a) (Set.singleton_nonempty b)
      (Set.disjoint_singleton.mpr hab)

/-- The every-union problem (answer whether the type lies in `A`, correctly on every promised
input) is the separation of `A` from its complement, for a type assignment with unique types. -/
theorem union_of_sep (T : Sentence → ℕ → Prop) (S : Set ℕ)
    (huniq : ∀ φ, Promised φ → ∀ τ τ', T φ τ → T φ τ' → τ = τ') (A : Set ℕ)
    (h : ¬ TypeSep T A (S \ A)) :
    ¬ ∃ D : Sentence →. Bool, Partrec D ∧
      ∀ φ, Promised φ → ∃ b ∈ D φ, (b = true ↔ ∃ τ ∈ A, T φ τ) := by
  rintro ⟨D, hD, hcorr⟩
  refine h ⟨D, hD, fun φ hφ τ hτ ht => ?_, fun φ hφ τ hτ ht => ?_⟩
  · obtain ⟨b, hb, hiff⟩ := hcorr φ hφ
    rwa [hiff.mpr ⟨τ, hτ, ht⟩] at hb
  · obtain ⟨b, hb, hiff⟩ := hcorr φ hφ
    cases b
    · exact hb
    · obtain ⟨τ', hτ', ht'⟩ := hiff.mp rfl
      exact absurd (huniq φ hφ τ τ' ht ht' ▸ hτ') hτ.2

/-! ### The witness order and the pair reduction -/

/-- The witness order `T1 ≺ T4 ≺ T3 ≺ T2`. -/
def wrank : ℕ → ℕ
  | 1 => 0
  | 4 => 1
  | 3 => 2
  | 2 => 3
  | _ => 4

section Reduction
variable (p : ℕ) [hp : Fact p.Prime] (K : Type) [Field K] [CharP K p]

/-- The pair reduction `c ↦ ψ_a ∨_* (ψ_b ∧ θ_{U(c)})`. -/
noncomputable def red2 (a b : ℕ) (c : Code) : Sentence :=
  join (wit p a) (conj (wit p b) (theta (univProg (Encodable.encode c))))

omit hp in
theorem red2_primrec (a b : ℕ) : Primrec (red2 p a b) :=
  (join_primrec _).comp ((conj_primrec _).comp (theta_primrec.comp
    (univProg_primrec.comp Primrec.encode)))

omit hp in
theorem red2_promised (a b : ℕ) (c : Code) : Promised (red2 p a b c) := by
  have hB : WF (conj (wit p b) (theta (univProg (Encodable.encode c)))) :=
    conj_WF (wit_WF p b) (theta_WF _)
  refine ⟨join_WF _ _ (wit_WF p a) hB, fun n hn h => ?_⟩
  rcases join_no_model _ _ n (wit_WF p a) hB hn h with h' | h'
  · exact wit_no_model p a hn h'
  · exact conj_no_model _ (wit_WF p b) (fun _ h => wit_no_model p b h) _ hn h'

omit hp [CharP K p] in
/-- The two-sided degree sandwich for the join (NS, every `n ≥ 1`). -/
theorem join_sandwich (A B : Sentence) (hA : WF A) (hB : WF B) :
    (∀ n, 1 ≤ n → max ((template A K).nsProfile n) ((template B K).nsProfile n) ≤
      (template (join A B) K).nsProfile n) ∧
    (∀ n, 1 ≤ n → (template (join A B) K).nsProfile n ≤
      max ((template A K).nsProfile n) ((template B K).nsProfile n) + 1) :=
  ⟨fun n hn => nsDegree_join_ge A B K n hA hB hn, fun n hn => nsDegree_join_le A B K n hA hB hn⟩

omit hp [CharP K p] in
/-- A non-halting `θ` block does not change the profile at any `n ≥ 1`. -/
theorem conj_prof_nonhalt (ψ : Sentence) (hψ : WF ψ) (P : Prog) (hP : ¬ P.Halts) (n : ℕ)
    (hn : 1 ≤ n) : (template (conj ψ (theta P)) K).nsProfile n = (template ψ K).nsProfile n := by
  obtain ⟨y, hy⟩ := (hasRoot_iff (theta P) K (n := n) (by omega)).mpr (switch_i P hP (by omega))
  exact nsDegree_conj_eq_left ψ (theta P) n K hψ (theta_WF P) y hy

/-- **Halting**: the join has the type of its first witness. -/
theorem red2_halt (a b : ℕ) (ha : a ∈ ({1, 2, 3, 4} : Set ℕ)) (c : Code)
    (h : (Code.eval c 0).Dom) : NSType (template (red2 p a b c) K) a := by
  have hB : WF (conj (wit p b) (theta (univProg (Encodable.encode c)))) :=
    conj_WF (wit_WF p b) (theta_WF _)
  obtain ⟨hlo, hhi⟩ := join_sandwich K _ _ (wit_WF p a) hB
  have hg : EventuallyBounded
      (template (conj (wit p b) (theta (univProg (Encodable.encode c)))) K).nsProfile :=
    conj_type_halt K _ _ ((eval_dom_iff_halts c).mp h)
  rw [nsType_iff_intrinsic p, red2, iType_sandwich hg hlo hhi]
  exact (nsType_iff_intrinsic p _ a).mp (wit_type p K a ha)

theorem bhat_le_five {n : ℕ} (hn : 1 ≤ n) (hpn : ¬ p ∣ n) :
    (template bhat K).nsProfile n ≤ (5 : ℕ) := by
  have := bhat_upper K (n := n) (by omega) hp.out (a := 0) (u := n) hpn (by simp)
  rw [pow_zero] at this
  exact (nsDegree_le_iff _ 5).mpr this

/-- **Non-halting**: for `a ≺ b` the join has the type of the second witness. -/
theorem red2_nonhalt (a b : ℕ) (ha : a ∈ ({1, 2, 3, 4} : Set ℕ)) (hb : b ∈ ({1, 2, 3, 4} : Set ℕ))
    (hab : wrank a < wrank b) (c : Code) (h : ¬ (Code.eval c 0).Dom) :
    NSType (template (red2 p a b c) K) b := by
  have hP : ¬ (univProg (Encodable.encode c)).Halts := fun h' => h ((eval_dom_iff_halts c).mpr h')
  have hB : WF (conj (wit p b) (theta (univProg (Encodable.encode c)))) :=
    conj_WF (wit_WF p b) (theta_WF _)
  obtain ⟨hlo, hhi⟩ := join_sandwich K _ _ (wit_WF p a) hB
  have heq := conj_prof_nonhalt K (wit p b) (wit_WF p b) _ hP
  have hlo' : ∀ n, 1 ≤ n → max ((template (wit p a) K).nsProfile n)
      ((template (wit p b) K).nsProfile n) ≤ (template (red2 p a b c) K).nsProfile n :=
    fun n hn => by rw [← heq n hn]; exact hlo n hn
  have hhi' : ∀ n, 1 ≤ n → (template (red2 p a b c) K).nsProfile n ≤
      max ((template (wit p a) K).nsProfile n) ((template (wit p b) K).nsProfile n) + 1 :=
    fun n hn => by rw [← heq n hn]; exact hhi n hn
  rw [nsType_iff_intrinsic p]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  by_cases ha1 : a = 1
  · -- a bounded first block: the type of `ψ_b`
    subst ha1
    have hg : EventuallyBounded (template (wit p 1) K).nsProfile := psi1_type p K
    rw [iType_sandwich (h := (template (wit p b) K).nsProfile) hg
      (fun n hn => by rw [max_comm]; exact hlo' n hn)
      (fun n hn => by rw [max_comm]; exact hhi' n hn)]
    exact (nsType_iff_intrinsic p _ b).mp (wit_type p K b (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; exact hb))
  · by_cases hb2 : b = 2
    · -- T2 dominates
      subst hb2
      exact iType2_mono (eta_type p K) fun n hn => le_trans (le_max_right _ _) (hlo' n hn)
    · -- the remaining pair is `(4, 3)`
      have h43 : a = 4 ∧ b = 3 := by
        rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
          simp_all [wrank]
      obtain ⟨rfl, rfl⟩ := h43
      refine iType3_of hp.out.two_le (max 5 p + 1) (eta_type p K) (fun n hn hpn => ?_)
        (fun n hn hpn => ?_)
      · refine le_trans (hhi' n hn) ?_
        have e : ((max 5 p + 1 : ℕ) : ℕ∞) = max ((5 : ℕ) : ℕ∞) (p : ℕ∞) + 1 := by
          rw [max_coe]; push_cast; rfl
        rw [e]
        have h1 := bhat_le_five p K hn hpn
        have h2 := psi3_le p K (n := n) (by omega) hpn
        change max ((template bhat K).nsProfile n) ((template (psi3 p) K).nsProfile n) + 1 ≤ _
        gcongr
      · rw [← psi3_eq_eta p K (by omega) hpn]
        exact le_trans (le_max_right _ _) (hlo' n hn)

end Reduction

/-! ### The theorems -/

section Final
variable (p : ℕ) [hp : Fact p.Prime] (K : Type) [Field K] [CharP K p]
include hp

omit hp in
theorem wrank_ne {a b : ℕ} (ha : a ∈ ({1, 2, 3, 4} : Set ℕ)) (hb : b ∈ ({1, 2, 3, 4} : Set ℕ))
    (hab : a ≠ b) : wrank a < wrank b ∨ wrank b < wrank a := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
    simp_all [wrank]

/-- **Every pair of distinct types** is undecidable (NS). -/
theorem undecidable_pair_NS (a b : ℕ) (ha : a ∈ ({1, 2, 3, 4} : Set ℕ))
    (hb : b ∈ ({1, 2, 3, 4} : Set ℕ)) (hab : a ≠ b) :
    ¬ TypeSep (fun φ τ => NSType (template φ K) τ) {a} {b} := by
  rintro ⟨D, hD, h1, h2⟩
  rcases wrank_ne ha hb hab with hlt | hlt
  · -- `D ∘ red2 a b` decides halting
    exact ComputablePred.halting_problem 0 (sep_decides hD h1 h2 (red2 p a b)
      (red2_primrec p a b).to_comp (red2_promised p a b) (fun c => (Code.eval c 0).Dom)
      (fun c hc => ⟨a, rfl, red2_halt p K a b ha c hc⟩)
      (fun c hc => ⟨b, rfl, red2_nonhalt p K a b ha hb hlt c hc⟩))
  · -- `D ∘ red2 b a` decides non-halting
    have hnot := sep_decides hD h1 h2 (red2 p b a) (red2_primrec p b a).to_comp
      (red2_promised p b a) (fun c => ¬ (Code.eval c 0).Dom)
      (fun c hc => ⟨a, rfl, red2_nonhalt p K b a hb ha hlt c hc⟩)
      (fun c hc => ⟨b, rfl, red2_halt p K b a hb c (not_not.mp hc)⟩)
    exact ComputablePred.halting_problem 0 (by simpa only [not_not] using hnot.not)

/-- **Every pair of nonempty disjoint type sets** is undecidable (NS). -/
theorem undecidable_disjoint_NS (A B : Set ℕ) (hA : A ⊆ {1, 2, 3, 4}) (hB : B ⊆ {1, 2, 3, 4})
    (hAne : A.Nonempty) (hBne : B.Nonempty) (hdisj : Disjoint A B) :
    ¬ TypeSep (fun φ τ => NSType (template φ K) τ) A B :=
  (pairs_iff_disjoint _ {1, 2, 3, 4}).mp
    (fun a ha b hb hab => undecidable_pair_NS p K a b ha hb hab) A B hA hB hAne hBne hdisj

theorem typeSep_PC_iff (A B : Set ℕ) :
    TypeSep (fun φ τ => PCType (template φ K) τ) A B ↔
      TypeSep (fun φ τ => NSType (template φ K) τ) A B := by
  unfold TypeSep
  simp only [pcType_iff_nsType p]

/-- **Every pair of distinct types** is undecidable (ordinary PC). -/
theorem undecidable_pair_PC (a b : ℕ) (ha : a ∈ ({1, 2, 3, 4} : Set ℕ))
    (hb : b ∈ ({1, 2, 3, 4} : Set ℕ)) (hab : a ≠ b) :
    ¬ TypeSep (fun φ τ => PCType (template φ K) τ) {a} {b} := by
  rw [typeSep_PC_iff p]
  exact undecidable_pair_NS p K a b ha hb hab

/-- **Every pair of nonempty disjoint type sets** is undecidable (ordinary PC). -/
theorem undecidable_disjoint_PC (A B : Set ℕ) (hA : A ⊆ {1, 2, 3, 4}) (hB : B ⊆ {1, 2, 3, 4})
    (hAne : A.Nonempty) (hBne : B.Nonempty) (hdisj : Disjoint A B) :
    ¬ TypeSep (fun φ τ => PCType (template φ K) τ) A B := by
  rw [typeSep_PC_iff p]
  exact undecidable_disjoint_NS p K A B hA hB hAne hBne hdisj

/-- The every-union theorem (NS) recovered as the case `B = {1,2,3,4} \ A` of the disjoint-set
theorem (a second proof of `undecidable_union_NS`, through the pair reductions). -/
theorem undecidable_union_NS_via_pairs (A : Set ℕ) (hA : A ⊆ {1, 2, 3, 4}) (hne : A.Nonempty)
    (hprop : ∃ τ ∈ ({1, 2, 3, 4} : Set ℕ), τ ∉ A) :
    ¬ ∃ D : Sentence →. Bool, Partrec D ∧
      ∀ φ, Promised φ → ∃ b ∈ D φ, (b = true ↔ ∃ τ ∈ A, NSType (template φ K) τ) := by
  obtain ⟨τ0, hτ0, hτ0A⟩ := hprop
  exact union_of_sep (fun φ τ => NSType (template φ K) τ) {1, 2, 3, 4}
    (fun φ _ τ τ' h h' => nsType_unique p _ h h') A
    (undecidable_disjoint_NS p K A ({1, 2, 3, 4} \ A) hA Set.diff_subset hne ⟨τ0, hτ0, hτ0A⟩
      Set.disjoint_sdiff_right)

/-- The every-union theorem (ordinary PC) through the pair reductions and the agreement of types. -/
theorem undecidable_union_PC_via_pairs (A : Set ℕ) (hA : A ⊆ {1, 2, 3, 4}) (hne : A.Nonempty)
    (hprop : ∃ τ ∈ ({1, 2, 3, 4} : Set ℕ), τ ∉ A) :
    ¬ ∃ D : Sentence →. Bool, Partrec D ∧
      ∀ φ, Promised φ → ∃ b ∈ D φ, (b = true ↔ ∃ τ ∈ A, PCType (template φ K) τ) := by
  simp only [pcType_iff_nsType p]
  exact undecidable_union_NS_via_pairs p K A hA hne hprop

end Final

end ClaudeUndec
