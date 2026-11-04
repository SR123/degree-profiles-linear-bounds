import DiagonalMoment
import Mathlib.Order.Hom.Set

namespace SelfContainedCycle051
open SelfContainedCycle035 SelfContainedCycle036 SelfContainedCycle037
open SelfContainedCycle038 SelfContainedCycle045 SelfContainedCycle047 SelfContainedCycle048 SelfContainedCycle050

/-- Column values strictly decrease along increasing occupied rows. -/
def Decreasing (S : Edges) : Prop :=
  ∀ e ∈ S, ∀ f ∈ S, e.1 < f.1 → f.2 < e.2

/-- The new row is genuinely unused; the move retains the column. -/
def moveRow (S : Edges) (e : ℕ × ℕ) (u : ℕ) : Edges :=
  insert (u,e.2) (S.erase e)

theorem moveRow_matching {S : Edges} {e : ℕ × ℕ} {u : ℕ}
    (hm : IsMatching S) (he : e ∈ S) (hu : u ∉ rows S) :
    IsMatching (moveRow S e u) := by
  have old_new : ∀ f ∈ S.erase e, f.1 ≠ u ∧ f.2 ≠ e.2 := by
    intro f hf
    obtain ⟨hne,hf⟩ := Finset.mem_erase.mp hf
    constructor
    · intro h
      exact hu (h ▸ Finset.mem_image.mpr ⟨f,hf,rfl⟩)
    · intro h
      exact hne (hm f hf e he (Or.inr h))
  intro x hx y hy h
  rcases Finset.mem_insert.mp hx with hx | hx
  · subst x
    rcases Finset.mem_insert.mp hy with hy | hy
    · exact hy.symm
    · obtain ⟨hr,hc⟩ := old_new y hy
      rcases h with h | h <;> simp_all
  · rcases Finset.mem_insert.mp hy with hy | hy
    · subst y
      obtain ⟨hr,hc⟩ := old_new x hx
      rcases h with h | h <;> simp_all
    · exact hm x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) h

theorem moveRow_card {S : Edges} {e : ℕ × ℕ} {u : ℕ}
    (he : e ∈ S) (hu : u ∉ rows S) : (moveRow S e u).card = S.card := by
  have hn : (u,e.2) ∉ S.erase e := by
    intro h
    exact hu (Finset.mem_image.mpr ⟨_,Finset.mem_of_mem_erase h,rfl⟩)
  simp only [moveRow,Finset.card_insert_of_notMem hn]
  exact Finset.card_erase_add_one he

theorem moveRow_subset {S : Edges} {e : ℕ × ℕ} {u : ℕ} {A B : Finset ℕ}
    (he : e ∈ S) (hS : S ⊆ A.product B) (hu : u ∈ A) :
    moveRow S e u ⊆ A.product B := by
  apply Finset.insert_subset
  · exact Finset.mem_product.mpr ⟨hu,(Finset.mem_product.mp (hS he)).2⟩
  · exact (Finset.erase_subset _ _).trans hS

/-- Strict coordinate-sum dominance is retained by any unchanged finite context. -/
theorem replace_weight_lt {S C M G : Edges} {H : ℕ}
    (hC : C ⊆ S) (hnew : (S \ C) ∪ M ⊆ G)
    (hG : ∀ e ∈ G, e.1+e.2 ≤ H) (hd : SumDominates C M) :
    weightSum G H ((S \ C) ∪ M) < weightSum G H S := by
  have hd' := sumDominates_union (P:=S \ C) Finset.sdiff_disjoint hd
  rw [Finset.sdiff_union_of_subset hC] at hd'
  exact sumDominates_weight_lt hnew hG hd'

theorem moveRow_weight_lt {S G : Edges} {e : ℕ × ℕ} {u H : ℕ}
    (he : e ∈ S) (hnew : moveRow S e u ⊆ G)
    (hG : ∀ f ∈ G, f.1+f.2 ≤ H) (hu : e.1 < u) :
    weightSum G H (moveRow S e u) < weightSum G H S := by
  have hd : SumDominates {e} {(u,e.2)} := by
    refine ⟨e,?_,?_⟩
    · simp only [Finset.mem_sdiff,Finset.mem_singleton]
      exact ⟨True.intro,fun h => by have h' := congrArg Prod.fst h; simp only at h'; omega⟩
    · intro f hf
      have hf' := Finset.mem_singleton.mp (Finset.mem_sdiff.mp hf).1
      subst f
      dsimp only
      omega
  have hn : (S \ {e}) ∪ {(u,e.2)} = moveRow S e u := by
    ext f
    simp [moveRow,or_comm,and_comm]
  have h := replace_weight_lt (Finset.singleton_subset_iff.mpr he) (hn ▸ hnew) hG hd
  simpa only [hn] using h

/-- Column moves use the same proved row move under transposition. -/
def moveCol (S : Edges) (e : ℕ × ℕ) (u : ℕ) : Edges :=
  transpose (moveRow (transpose S) e.swap u)

theorem moveCol_valid {S : Edges} {e : ℕ × ℕ} {u : ℕ}
    (hm : IsMatching S) (he : e ∈ S) (hu : u ∉ cols S) :
    IsMatching (moveCol S e u) ∧ (moveCol S e u).card = S.card := by
  have he' : e.swap ∈ transpose S := by
    exact Finset.mem_map.mpr ⟨e,he,rfl⟩
  have hu' : u ∉ rows (transpose S) := by simpa only [rows_transpose] using hu
  constructor
  · exact (matching_transpose _).mpr (moveRow_matching ((matching_transpose _).mpr hm) he' hu')
  · simpa [moveCol] using moveRow_card he' hu'

theorem moveCol_weight_lt {S G : Edges} {e : ℕ × ℕ} {u H : ℕ}
    (he : e ∈ S) (hnew : moveCol S e u ⊆ G)
    (hG : ∀ f ∈ G, f.1+f.2 ≤ H) (hu : e.2 < u) :
    weightSum G H (moveCol S e u) < weightSum G H S := by
  have he' : e.swap ∈ transpose S := Finset.mem_map.mpr ⟨e,he,rfl⟩
  have hn : moveRow (transpose S) e.swap u ⊆ transpose G := by
    have ht : transpose (moveCol S e u) ⊆ transpose G := Finset.map_subset_map.mpr hnew
    simpa only [moveCol,transpose_transpose] using ht
  have hg : ∀ f ∈ transpose G, f.1+f.2 ≤ H := by
    intro f hf
    obtain ⟨g,hg,rfl⟩ := Finset.mem_map.mp hf
    simpa [swapEmbedding,Nat.add_comm] using hG g hg
  have h := moveRow_weight_lt he' hn hg hu
  have hleft := weightSum_transpose G (moveCol S e u) H
  simp only [moveCol,transpose_transpose] at hleft
  rw [hleft,weightSum_transpose] at h
  exact h

/-- Both crossed edges come after the lower-left edge of an increasing pair. -/
theorem increasing_pair_dominates {e f : ℕ × ℕ}
    (hr : e.1 < f.1) (hc : e.2 < f.2) :
    SumDominates {e,f} {(e.1,f.2),(f.1,e.2)} := by
  refine ⟨e,?_,?_⟩
  · simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_singleton,not_or]
    refine ⟨Or.inl True.intro,?_,?_⟩
    · intro h
      have h' := congrArg Prod.snd h
      simp only at h'
      omega
    · intro h
      have h' := congrArg Prod.fst h
      simp only at h'
      omega
  · intro x hx
    rcases Finset.mem_insert.mp (Finset.mem_sdiff.mp hx).1 with hx | hx
    · subst x
      dsimp only
      omega
    · have hx' := Finset.mem_singleton.mp hx
      subst x
      dsimp only
      omega

/-- The minimum-row obstruction always supplies a legal improving row move. -/
theorem improve_used_minimum_row {S G : Edges} {A B : Finset ℕ} {a H : ℕ}
    (hm : IsMatching S) (hS : S ⊆ A.product B)
    (hcard : S.card+1 = A.card) (hmin : ∀ u ∈ A, a ≤ u)
    (ha : a ∈ rows S) (hAB : A.product B ⊆ G) (hG : ∀ e ∈ G, e.1+e.2 ≤ H) :
    ∃ Q, IsMatching Q ∧ Q ⊆ A.product B ∧ Q.card=S.card ∧
      weightSum G H Q < weightSum G H S := by
  have hr : rows S ⊆ A := by
    intro i hi
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hi
    exact (Finset.mem_product.mp (hS he)).1
  have hdiff : (A \ rows S).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_sdiff_of_subset hr,matching_rows_card hm]
    omega
  obtain ⟨u,hu⟩ := hdiff
  obtain ⟨huA,huS⟩ := Finset.mem_sdiff.mp hu
  obtain ⟨e,he,hea⟩ := Finset.mem_image.mp ha
  have hu : e.1 < u := by
    have hl := hmin u huA
    have hn : a ≠ u := fun h => huS (h ▸ ha)
    omega
  refine ⟨moveRow S e u,moveRow_matching hm he huS,moveRow_subset he hS huA,
    moveRow_card he huS,?_⟩
  exact moveRow_weight_lt he ((moveRow_subset he hS huA).trans hAB) hG hu

/-- Uniqueness of decreasing matchings on fixed occupied row and column sets. -/
theorem decreasing_matching_unique {S T : Edges}
    (hmS : IsMatching S) (hmT : IsMatching T) (hS : Decreasing S) (hT : Decreasing T)
    (hr : rows S = rows T) (hc : cols S = cols T) : S=T := by
  let f := supportedEquiv S hmS (rows T) (cols T) hr hc
  let g := matchingEquiv T hmT
  have hfg : ∀ M (hm : IsMatching M) (hd : Decreasing M)
      (hr : rows M = rows T) (hc : cols M = cols T),
      StrictMono (show rows T → OrderDual (cols T) from supportedEquiv M hm (rows T) (cols T) hr hc) := by
    intro M hm hd hr hc i j hij
    have hi : ((i:ℕ),(supportedEquiv M hm (rows T) (cols T) hr hc i:ℕ)) ∈ M := by
      have hx := (mem_bijectionGraph (supportedEquiv M hm (rows T) (cols T) hr hc)
        ((i:ℕ),(supportedEquiv M hm (rows T) (cols T) hr hc i:ℕ))).mpr ⟨i,rfl⟩
      simpa only [supportedEquiv_graph] using hx
    have hj : ((j:ℕ),(supportedEquiv M hm (rows T) (cols T) hr hc j:ℕ)) ∈ M := by
      have hx := (mem_bijectionGraph (supportedEquiv M hm (rows T) (cols T) hr hc)
        ((j:ℕ),(supportedEquiv M hm (rows T) (cols T) hr hc j:ℕ))).mpr ⟨j,rfl⟩
      simpa only [supportedEquiv_graph] using hx
    exact hd _ hi _ hj hij
  let F : rows T ≃o OrderDual (cols T) :=
    StrictMono.orderIsoOfSurjective _ (hfg S hmS hS hr hc) f.surjective
  let G : rows T ≃o OrderDual (cols T) :=
    StrictMono.orderIsoOfSurjective _ (hfg T hmT hT rfl rfl) g.surjective
  have hFG : F=G := Subsingleton.elim _ _
  have hfun : f=g := by
    apply Equiv.ext
    intro i
    exact congrArg (fun k : rows T ≃o OrderDual (cols T) => k i) hFG
  calc
    S = bijectionGraph f := (supportedEquiv_graph _ _ _ _ _ _).symm
    _ = bijectionGraph g := congrArg bijectionGraph hfun
    _ = T := matchingEquiv_graph _ _

/-- Failure of decreasingness supplies an actual increasing pair in a matching. -/
theorem exists_increasing_pair {S : Edges} (hm : IsMatching S) (h : ¬ Decreasing S) :
    ∃ e ∈ S, ∃ f ∈ S, e.1 < f.1 ∧ e.2 < f.2 := by
  unfold Decreasing at h
  push_neg at h
  obtain ⟨e,he,f,hf,hr,hc⟩ := h
  refine ⟨e,he,f,hf,hr,?_⟩
  have hn : e.2 ≠ f.2 := by
    intro h
    have heq := hm e he f hf (Or.inr h)
    rw [heq] at hr
    exact (lt_irrefl _ hr)
  omega

/-- Actual height levels meet the uniqueness theorem's order hypothesis. -/
theorem heightLevel_decreasing {R : Edges} (hm : IsMatching R) (t : ℕ) :
    Decreasing (heightLevel R t) := fun _ he _ hf hr => level_decreasing hm he hf hr

/-- All three moves have strict direction on concrete nonempty inputs. -/
theorem improving_examples :
    moveRow {(1,3),(3,1)} (1,3) 2 = {(2,3),(3,1)} ∧
    moveCol {(2,1)} (2,1) 3 = {(2,3)} ∧
    weightSum (grid 3 3) 6 {(2,3),(3,1)} < weightSum (grid 3 3) 6 {(1,3),(3,1)} ∧
    weightSum (grid 3 3) 6 {(2,3)} < weightSum (grid 3 3) 6 {(2,1)} ∧
    weightSum (grid 3 3) 6 {(1,3),(3,1)} < weightSum (grid 3 3) 6 {(1,1),(3,3)} := by decide

/-- Replace an increasing pair by its crossed pairing. -/
def crossPair (S : Edges) (e f : ℕ × ℕ) : Edges :=
  (S \ {e,f}) ∪ {(e.1,f.2),(f.1,e.2)}

theorem crossPair_valid {S : Edges} {e f : ℕ × ℕ} {A B : Finset ℕ}
    (hm : IsMatching S) (he : e ∈ S) (hf : f ∈ S)
    (hr : e.1 < f.1) (hc : e.2 < f.2) (hS : S ⊆ A.product B) :
    IsMatching (crossPair S e f) ∧ crossPair S e f ⊆ A.product B ∧
      (crossPair S e f).card = S.card := by
  have hneq : e ≠ f := by intro h; subst f; omega
  have hcneq : (e.1,f.2) ≠ (f.1,e.2) := by
    intro h
    have h' := congrArg Prod.fst h
    simp only at h'
    omega
  have hcross : IsMatching {(e.1,f.2),(f.1,e.2)} := by
    intro x hx y hy hh
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · rcases hh with hh | hh <;> dsimp only at hh <;> omega
    · rcases hh with hh | hh <;> dsimp only at hh <;> omega
    · rfl
  have hn : ∀ x ∈ S \ {e,f}, ∀ y ∈ ({(e.1,f.2),(f.1,e.2)} : Edges),
      x.1 ≠ y.1 ∧ x.2 ≠ y.2 := by
    intro x hx y hy
    obtain ⟨hxS,hxC⟩ := Finset.mem_sdiff.mp hx
    have hxe : x ≠ e := by intro h; exact hxC (by simp [h])
    have hxf : x ≠ f := by intro h; exact hxC (by simp [h])
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact ⟨fun h => hxe (hm x hxS e he (Or.inl h)),
        fun h => hxf (hm x hxS f hf (Or.inr h))⟩
    · have hy' := Finset.mem_singleton.mp hy
      subst y
      exact ⟨fun h => hxf (hm x hxS f hf (Or.inl h)),
        fun h => hxe (hm x hxS e he (Or.inr h))⟩
  have hd : Disjoint (S \ {e,f}) {(e.1,f.2),(f.1,e.2)} := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (hn x hx x hy).1 rfl
  refine ⟨?_,?_,?_⟩
  · intro x hx y hy hh
    rcases Finset.mem_union.mp hx with hx | hx <;>
      rcases Finset.mem_union.mp hy with hy | hy
    · exact hm x (Finset.mem_sdiff.mp hx).1 y (Finset.mem_sdiff.mp hy).1 hh
    · rcases hh with hh | hh
      · exact ((hn x hx y hy).1 hh).elim
      · exact ((hn x hx y hy).2 hh).elim
    · rcases hh with hh | hh
      · exact ((hn y hy x hx).1 hh.symm).elim
      · exact ((hn y hy x hx).2 hh.symm).elim
    · exact hcross x hx y hy hh
  · apply Finset.union_subset ((Finset.sdiff_subset).trans hS)
    have heAB := Finset.mem_product.mp (hS he)
    have hfAB := Finset.mem_product.mp (hS hf)
    apply Finset.insert_subset
    · exact Finset.mem_product.mpr ⟨heAB.1,hfAB.2⟩
    · exact Finset.singleton_subset_iff.mpr (Finset.mem_product.mpr ⟨hfAB.1,heAB.2⟩)
  · have hsub : ({e,f} : Edges) ⊆ S := by simp [Finset.insert_subset_iff,he,hf]
    have hpair : ({e,f} : Edges).card = 2 := by simp [hneq]
    have hcrosscard : ({(e.1,f.2),(f.1,e.2)} : Edges).card = 2 := by simp [hcneq]
    have hle := Finset.card_le_card hsub
    rw [crossPair,Finset.card_union_of_disjoint hd,Finset.card_sdiff_of_subset hsub,
      hpair,hcrosscard]
    omega

theorem crossPair_weight_lt {S G : Edges} {e f : ℕ × ℕ} {H : ℕ}
    (he : e ∈ S) (hf : f ∈ S) (hr : e.1 < f.1) (hc : e.2 < f.2)
    (hnew : crossPair S e f ⊆ G) (hG : ∀ x ∈ G, x.1+x.2 ≤ H) :
    weightSum G H (crossPair S e f) < weightSum G H S := by
  exact replace_weight_lt (by simp [Finset.insert_subset_iff,he,hf]) hnew hG
    (increasing_pair_dominates hr hc)

/-- The column counterpart retains support, cardinality, matching and strict decrease. -/
theorem improve_used_minimum_col {S G : Edges} {A B : Finset ℕ} {b H : ℕ}
    (hm : IsMatching S) (hS : S ⊆ A.product B)
    (hcard : S.card+1 = B.card) (hmin : ∀ u ∈ B, b ≤ u)
    (hb : b ∈ cols S) (hAB : A.product B ⊆ G) (hG : ∀ e ∈ G, e.1+e.2 ≤ H) :
    ∃ Q, IsMatching Q ∧ Q ⊆ A.product B ∧ Q.card=S.card ∧
      weightSum G H Q < weightSum G H S := by
  have hprod : transpose (A.product B) = B.product A := by
    ext e
    simp [transpose,swapEmbedding,Finset.mem_map,Prod.ext_iff,and_comm,and_assoc]
  have hs : transpose S ⊆ B.product A := by
    rw [← hprod]
    exact Finset.map_subset_map.mpr hS
  have hc : (transpose S).card+1=B.card := by simpa using hcard
  have hrow : b ∈ rows (transpose S) := by simpa only [rows_transpose] using hb
  have hAB' : B.product A ⊆ transpose G := by
    rw [← hprod]
    exact Finset.map_subset_map.mpr hAB
  have hbound : ∀ e ∈ transpose G, e.1+e.2 ≤ H := by
    intro e he
    obtain ⟨f,hf,rfl⟩ := Finset.mem_map.mp he
    simpa [swapEmbedding,Nat.add_comm] using hG f hf
  obtain ⟨Q,hQ,hQA,hQc,hQw⟩ := improve_used_minimum_row
    ((matching_transpose _).mpr hm) hs hc hmin hrow hAB' hbound
  refine ⟨transpose Q,(matching_transpose _).mpr hQ,?_,by simpa using hQc,?_⟩
  · have h := Finset.map_subset_map (f:=swapEmbedding) |>.mpr hQA
    have hprod' : transpose (B.product A)=A.product B := by
      rw [← hprod,transpose_transpose]
    simpa only [← hprod',transpose] using h
  · have hleft := weightSum_transpose G (transpose Q) H
    simp only [transpose_transpose] at hleft
    have hright := weightSum_transpose G S H
    simpa only [hleft,hright] using hQw

/-- With one unused label, omitting the minimum fixes the entire occupied support. -/
theorem occupied_rows_eq_erase {S : Edges} {A B : Finset ℕ} {a : ℕ}
    (hm : IsMatching S) (hS : S ⊆ A.product B) (ha : a ∈ A)
    (hcard : S.card+1=A.card) (hna : a ∉ rows S) : rows S=A.erase a := by
  have hsub : rows S ⊆ A.erase a := by
    intro i hi
    refine Finset.mem_erase.mpr ⟨?_,?_⟩
    · intro h
      exact hna (h ▸ hi)
    · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hi
      exact (Finset.mem_product.mp (hS he)).1
  apply Finset.eq_of_subset_of_card_le hsub
  rw [matching_rows_card hm,Finset.card_erase_of_mem ha]
  omega

/-- Every weight minimizer is the decreasing matching omitting both block minima. -/
theorem block_minimizer_unique {S L G : Edges} {A B : Finset ℕ} {a b H : ℕ}
    (hm : IsMatching S) (hS : S ⊆ A.product B)
    (hmL : IsMatching L) (hL : Decreasing L)
    (hAr : rows L=A.erase a) (hBc : cols L=B.erase b)
    (ha : a ∈ A) (hb : b ∈ B) (hminA : ∀ u ∈ A, a ≤ u)
    (hminB : ∀ u ∈ B, b ≤ u)
    (hcardA : S.card+1=A.card) (hcardB : S.card+1=B.card)
    (hAB : A.product B ⊆ G) (hG : ∀ e ∈ G, e.1+e.2 ≤ H)
    (hminimal : ∀ Q, IsMatching Q → Q ⊆ A.product B → Q.card=S.card →
      weightSum G H S ≤ weightSum G H Q) : S=L := by
  have hna : a ∉ rows S := by
    intro h
    obtain ⟨Q,hQ,hQA,hQc,hQw⟩ := improve_used_minimum_row hm hS hcardA hminA h hAB hG
    exact (not_lt_of_ge (hminimal Q hQ hQA hQc)) hQw
  have hnb : b ∉ cols S := by
    intro h
    obtain ⟨Q,hQ,hQA,hQc,hQw⟩ := improve_used_minimum_col hm hS hcardB hminB h hAB hG
    exact (not_lt_of_ge (hminimal Q hQ hQA hQc)) hQw
  have hdec : Decreasing S := by
    by_contra h
    obtain ⟨e,he,f,hf,hr,hc⟩ := exists_increasing_pair hm h
    obtain ⟨hQ,hQA,hQc⟩ := crossPair_valid hm he hf hr hc hS
    have hw := crossPair_weight_lt he hf hr hc (hQA.trans hAB) hG
    exact (not_lt_of_ge (hminimal _ hQ hQA hQc)) hw
  have hrows := occupied_rows_eq_erase hm hS ha hcardA hna
  have hcols : cols S=B.erase b := by
    have ht : transpose S ⊆ B.product A := by
      intro e he
      obtain ⟨f,hf,rfl⟩ := Finset.mem_map.mp he
      exact Finset.mem_product.mpr ⟨(Finset.mem_product.mp (hS hf)).2,(Finset.mem_product.mp (hS hf)).1⟩
    have h := occupied_rows_eq_erase ((matching_transpose _).mpr hm) ht hb
      (by simpa using hcardB) (by simpa only [rows_transpose] using hnb)
    simpa only [rows_transpose] using h
  exact decreasing_matching_unique hm hmL hdec hL (hrows.trans hAr.symm) (hcols.trans hBc.symm)

/-- The finite block minimum is proved, with no minimality or weight premise. -/
theorem strict_block_minimum {S L G : Edges} {A B : Finset ℕ} {a b H : ℕ}
    (hm : IsMatching S) (hS : S ⊆ A.product B)
    (hmL : IsMatching L) (hL : Decreasing L)
    (hAr : rows L=A.erase a) (hBc : cols L=B.erase b)
    (ha : a ∈ A) (hb : b ∈ B) (hminA : ∀ u ∈ A, a ≤ u)
    (hminB : ∀ u ∈ B, b ≤ u)
    (hcardA : S.card+1=A.card) (hcardB : S.card+1=B.card)
    (hAB : A.product B ⊆ G) (hG : ∀ e ∈ G, e.1+e.2 ≤ H) (hne : S ≠ L) :
    weightSum G H L < weightSum G H S := by
  let F := (A.product B).powerset.filter (fun Q => IsMatching Q ∧ Q.card=S.card)
  have hmem : ∀ Q, Q ∈ F ↔ Q ⊆ A.product B ∧ IsMatching Q ∧ Q.card=S.card := by
    intro Q
    simp only [F,Finset.mem_filter,Finset.mem_powerset]
  have hnon : F.Nonempty := ⟨S,(hmem S).mpr ⟨hS,hm,rfl⟩⟩
  obtain ⟨M,hM,hmin⟩ := Finset.exists_min_image F (weightSum G H) hnon
  obtain ⟨hMA,hmM,hMc⟩ := (hmem M).mp hM
  have hminimal : ∀ Q, IsMatching Q → Q ⊆ A.product B → Q.card=M.card →
      weightSum G H M ≤ weightSum G H Q := by
    intro Q hQ hQA hQc
    exact hmin Q ((hmem Q).mpr ⟨hQA,hQ,hQc.trans hMc⟩)
  have heq : M=L := block_minimizer_unique hmM hMA hmL hL hAr hBc ha hb hminA hminB
    (by omega) (by omega) hAB hG hminimal
  have hle : weightSum G H L ≤ weightSum G H S := by
    rw [← heq]
    exact hmin S ((hmem S).mpr ⟨hS,hm,rfl⟩)
  apply lt_of_le_of_ne hle
  intro hw
  have hminimalS : ∀ Q, IsMatching Q → Q ⊆ A.product B → Q.card=S.card →
      weightSum G H S ≤ weightSum G H Q := by
    intro Q hQ hQA hQc
    rw [← hw,← heq]
    exact hmin Q ((hmem Q).mpr ⟨hQA,hQ,hQc⟩)
  exact hne (block_minimizer_unique hm hS hmL hL hAr hBc ha hb hminA hminB
    hcardA hcardB hAB hG hminimalS)

section Actual
open SelfContainedCycle049
variable {N : ℕ} {R : Edges} (hm : IsMatching R) (hR : R ⊆ grid N N)
    (ht : chosenRewrite R = .terminal)

theorem actual_level_strict_minimum (t : Fin (chainHeight R)) {S : Edges}
    (hS : IsMatching S) (hsub : S ⊆ (rowBlock hm hR ht t).product (colBlock hm hR ht t))
    (hc : S.card=(heightLevel R (t.val+1)).card) (hne : S ≠ heightLevel R (t.val+1)) :
    weightSum (grid N N) (N+N) (heightLevel R (t.val+1)) <
      weightSum (grid N N) (N+N) S := by
  apply strict_block_minimum hS hsub (level_matching hm _) (heightLevel_decreasing hm _)
    (a:=rowAnchor hm hR ht t) (b:=colAnchor hm hR ht t)
  · simp [rowBlock,rowAnchor_not_level hm hR ht t _]
  · simp [colBlock,colAnchor_not_level hm hR ht t _]
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_self _ _
  · exact fun _ hi => rowAnchor_is_min hm hR ht t hi
  · exact fun _ hi => colAnchor_is_min hm hR ht t hi
  · rw [hc,rowBlock_card]
  · rw [hc,colBlock_card]
  · intro e he
    obtain ⟨hi,hj⟩ := Finset.mem_product.mp he
    exact Finset.mem_product.mpr ⟨rowBlock_subset hm hR ht t hi,colBlock_subset hm hR ht t hj⟩
  · exact grid_sum_bound N N
  · exact hne

def momentPart (P : Edges) (t : Fin (chainHeight R)) : Edges :=
  P.filter (fun e => e.1 ∈ rowBlock hm hR ht t)

theorem momentPart_rows (P : Edges) (t : Fin (chainHeight R)) :
    rows (momentPart hm hR ht P t)=rowBlock hm hR ht t ∩ rows P := by
  ext i
  simp only [rows,momentPart,Finset.mem_image,Finset.mem_filter,Finset.mem_inter]
  constructor
  · rintro ⟨e,⟨he,hi⟩,rfl⟩
    exact ⟨hi,e,he,rfl⟩
  · rintro ⟨hi,e,he,rfl⟩
    exact ⟨e,⟨he,hi⟩,rfl⟩

theorem momentParts_disjoint (P : Edges) {s t : Fin (chainHeight R)} (hne : s ≠ t) :
    Disjoint (momentPart hm hR ht P s) (momentPart hm hR ht P t) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  exact Finset.disjoint_left.mp (rowBlocks_disjoint hm hR ht hne)
    (Finset.mem_filter.mp he).2 (Finset.mem_filter.mp hf).2

theorem momentPart_valid (P : Edges) (hc : P.card=R.card)
    (hv : blockMoment hm hR ht P ≠ 0) (t : Fin (chainHeight R)) :
    IsMatching (momentPart hm hR ht P t) ∧
      momentPart hm hR ht P t ⊆ (rowBlock hm hR ht t).product (colBlock hm hR ht t) ∧
      (momentPart hm hR ht P t).card = (heightLevel R (t.val+1)).card := by
  have hP := (matching_grid_of_nonzero hm hR ht P hv).1
  have hmp : IsMatching (momentPart hm hR ht P t) := matching_subset hP (Finset.filter_subset _ _)
  refine ⟨hmp,?_,?_⟩
  · intro e he
    obtain ⟨heP,het⟩ := Finset.mem_filter.mp he
    obtain ⟨s,hes,hec⟩ := exact_degree_edge_support hm hR ht P hc hv heP
    have hst : s=t := by
      by_contra h
      exact Finset.disjoint_left.mp (rowBlocks_disjoint hm hR ht h) hes het
    subst s
    exact Finset.mem_product.mpr ⟨het,hec⟩
  · rw [← matching_rows_card hmp,momentPart_rows]
    exact exact_degree_occupied_card hm hR ht P hc hv t

theorem momentParts_cover (P : Edges) (hc : P.card=R.card)
    (hv : blockMoment hm hR ht P ≠ 0) :
    Finset.univ.biUnion (momentPart hm hR ht P)=P := by
  ext e
  constructor
  · intro h
    obtain ⟨t,_,he⟩ := Finset.mem_biUnion.mp h
    exact (Finset.mem_filter.mp he).1
  · intro he
    obtain ⟨t,het,_⟩ := exact_degree_edge_support hm hR ht P hc hv he
    exact Finset.mem_biUnion.mpr ⟨t,Finset.mem_univ _,Finset.mem_filter.mpr ⟨he,het⟩⟩

theorem momentParts_weight (P : Edges) (hc : P.card=R.card)
    (hv : blockMoment hm hR ht P ≠ 0) :
    (∑ t : Fin (chainHeight R),weightSum (grid N N) (N+N) (momentPart hm hR ht P t)) =
      weightSum (grid N N) (N+N) P := by
  unfold weightSum
  rw [← Finset.sum_biUnion (fun s _ t _ h => momentParts_disjoint hm hR ht P h),
    momentParts_cover hm hR ht P hc hv]

theorem levels_weight :
    (∑ t : Fin (chainHeight R),weightSum (grid N N) (N+N) (heightLevel R (t.val+1))) =
      weightSum (grid N N) (N+N) R := by
  unfold weightSum
  have hdisj : ∀ s ∈ (Finset.univ : Finset (Fin (chainHeight R))),
      ∀ t ∈ Finset.univ, s ≠ t → Disjoint (heightLevel R (s.val+1)) (heightLevel R (t.val+1)) := by
    intro s _ t _ h
    apply levels_disjoint
    intro heq
    apply h
    apply Fin.ext
    omega
  rw [← Finset.sum_biUnion (fun s hs t ht h => hdisj s hs t ht h),levels_cover]

/-- The actual signed moment has its unique strict weight minimum at R in degree |R|. -/
theorem exact_degree_moment_strict_minimum (P : Edges) (hc : P.card=R.card)
    (hv : blockMoment hm hR ht P ≠ 0) (hne : P ≠ R) :
    weightSum (grid N N) (N+N) R < weightSum (grid N N) (N+N) P := by
  have hle : ∀ t : Fin (chainHeight R),
      weightSum (grid N N) (N+N) (heightLevel R (t.val+1)) ≤
      weightSum (grid N N) (N+N) (momentPart hm hR ht P t) := by
    intro t
    by_cases heq : momentPart hm hR ht P t=heightLevel R (t.val+1)
    · rw [heq]
    · obtain ⟨hmp,hsub,hcard⟩ := momentPart_valid hm hR ht P hc hv t
      exact (actual_level_strict_minimum hm hR ht t hmp hsub hcard heq).le
  have hdif : ∃ t : Fin (chainHeight R), momentPart hm hR ht P t ≠ heightLevel R (t.val+1) := by
    by_contra h
    push_neg at h
    apply hne
    calc
      P = Finset.univ.biUnion (momentPart hm hR ht P) := (momentParts_cover hm hR ht P hc hv).symm
      _ = Finset.univ.biUnion (fun t : Fin (chainHeight R) => heightLevel R (t.val+1)) := by
        apply Finset.biUnion_congr rfl
        intro t _
        exact h t
      _ = R := levels_cover R
  obtain ⟨t,htdiff⟩ := hdif
  obtain ⟨hmp,hsub,hcard⟩ := momentPart_valid hm hR ht P hc hv t
  have hlt := actual_level_strict_minimum hm hR ht t hmp hsub hcard htdiff
  have hsum := Finset.sum_lt_sum (fun t _ => hle t) ⟨t,Finset.mem_univ t,hlt⟩
  rw [levels_weight,momentParts_weight hm hR ht P hc hv] at hsum
  exact hsum
end Actual

/-- A distinct same-degree matching has a proved nonzero moment and strict larger weight. -/
theorem actual_off_diagonal_nonvacuity :
    blockMoment example_matching example_grid example_terminal {(3,5),(4,3),(2,2)} ≠ 0 ∧
    weightSum (grid 6 6) 12 exampleMatching <
      weightSum (grid 6 6) 12 {(3,5),(4,3),(2,2)} := by
  let P : Edges := {(3,5),(4,3),(2,2)}
  let σ := diagonalChoice example_matching example_grid example_terminal
  have hp : P ⊆ blockPermutation example_matching example_grid example_terminal σ := by
    dsimp only [σ]
    rw [example_global_graph]
    decide
  have hcount : ∀ t : Fin (chainHeight exampleMatching),
      (rowBlock example_matching example_grid example_terminal t \ rows P).card ≤ 1 := by
    intro t
    have hb : t.val < 2 := by simpa only [example_levels.1] using t.isLt
    have ht : t=⟨0,by decide⟩ ∨ t=⟨1,by decide⟩ := by
      by_cases h : t.val=0
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext (by change t.val=1; omega))
    rcases ht with rfl | rfl
    · rw [example_blocks.1]
      decide
    · rw [example_blocks.2.2.1]
      decide
  have hu : ∀ τ, P ⊆ blockPermutation example_matching example_grid example_terminal τ → τ=σ := by
    intro τ hτ
    exact SelfContainedCycle049.choices_eq_of_containing _ _ _ P hcount τ σ hτ hp
  have heq := SelfContainedCycle049.moment_eq_weight_of_unique
    example_matching example_grid example_terminal P σ hp hu
  have hv : blockMoment example_matching example_grid example_terminal P ≠ 0 := by
    rw [heq]
    exact (SelfContainedCycle049.blockWeight_isUnit _ _ _ σ).ne_zero
  refine ⟨hv,?_⟩
  exact exact_degree_moment_strict_minimum _ _ _ P (by decide) hv (by decide)

end SelfContainedCycle051
