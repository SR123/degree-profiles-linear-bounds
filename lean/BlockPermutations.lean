import LevelAnchors
import Mathlib.GroupTheory.Perm.Sign

namespace SelfContainedCycle048
open SelfContainedCycle035 SelfContainedCycle036 SelfContainedCycle037
open SelfContainedCycle038 SelfContainedCycle045 SelfContainedCycle047

/-- The actual finite edge graph of a bijection between two finite label sets. -/
def bijectionGraph {A B : Finset ℕ} (f : A ≃ B) : Edges :=
  Finset.univ.image (fun i : A => ((i:ℕ),(f i:ℕ)))

theorem mem_bijectionGraph {A B : Finset ℕ} (f : A ≃ B) (e : ℕ × ℕ) :
    e ∈ bijectionGraph f ↔ ∃ i : A, ((i:ℕ),(f i:ℕ)) = e := by
  simp only [bijectionGraph,Finset.mem_image,Finset.mem_univ,true_and]

@[simp] theorem graph_pair_mem {A B : Finset ℕ} (f : A ≃ B) (i : A) (j : ℕ) :
    ((i:ℕ),j) ∈ bijectionGraph f ↔ (f i:ℕ) = j := by
  rw [mem_bijectionGraph]
  constructor
  · rintro ⟨k,h⟩
    have hki : k=i := Subtype.ext (congrArg Prod.fst h)
    subst k
    exact congrArg Prod.snd h
  · intro h
    exact ⟨i,Prod.ext rfl h⟩

theorem graph_coordinate_membership {A B : Finset ℕ} (f : A ≃ B) {e : ℕ × ℕ}
    (he : e ∈ bijectionGraph f) : e.1 ∈ A ∧ e.2 ∈ B := by
  obtain ⟨i,rfl⟩ := (mem_bijectionGraph f e).mp he
  exact ⟨i.property,(f i).property⟩

theorem bijectionGraph_matching {A B : Finset ℕ} (f : A ≃ B) : IsMatching (bijectionGraph f) := by
  intro e he g hg h
  obtain ⟨i,rfl⟩ := (mem_bijectionGraph f e).mp he
  obtain ⟨j,rfl⟩ := (mem_bijectionGraph f g).mp hg
  have hij : i=j := by
    rcases h with h | h
    · exact Subtype.ext h
    · exact f.injective (Subtype.ext h)
  subst j
  rfl

theorem bijectionGraph_rows {A B : Finset ℕ} (f : A ≃ B) : rows (bijectionGraph f) = A := by
  ext i
  constructor
  · intro hi
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hi
    exact (graph_coordinate_membership f he).1
  · intro hi
    exact Finset.mem_image.mpr ⟨(i,(f ⟨i,hi⟩:ℕ)),(graph_pair_mem f ⟨i,hi⟩ _).mpr rfl,rfl⟩

theorem bijectionGraph_cols {A B : Finset ℕ} (f : A ≃ B) : cols (bijectionGraph f) = B := by
  ext j
  constructor
  · intro hj
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hj
    exact (graph_coordinate_membership f he).2
  · intro hj
    let i := f.symm ⟨j,hj⟩
    have hf : (f i:ℕ) = j := congrArg Subtype.val (f.apply_symm_apply ⟨j,hj⟩)
    exact Finset.mem_image.mpr ⟨((i:ℕ),j),(graph_pair_mem f i j).mpr hf,rfl⟩

theorem bijectionGraph_injective {A B : Finset ℕ} :
    Function.Injective (@bijectionGraph A B) := by
  intro f g h
  apply Equiv.ext
  intro i
  apply Subtype.ext
  have he : ((i:ℕ),(f i:ℕ)) ∈ bijectionGraph g := by
    rw [← h]; exact (graph_pair_mem f i _).mpr rfl
  exact ((graph_pair_mem g i _).mp he).symm

/-- A fixed increasing bijection, including empty finite label sets. -/
def orderedBijection (A B : Finset ℕ) (h : A.card = B.card) : A ≃ B :=
  (A.orderIsoOfFin rfl).toEquiv.symm.trans (B.orderIsoOfFin h.symm).toEquiv

section Join
variable {ι : Type*} [Fintype ι]

/-- Join actual edge graphs over finitely many disjoint paired parts. -/
def joinGraphs (A B : ι → Finset ℕ) (f : ∀ t, A t ≃ B t) : Edges :=
  Finset.univ.biUnion (fun t => bijectionGraph (f t))

theorem mem_joinGraphs (A B : ι → Finset ℕ) (f : ∀ t, A t ≃ B t) (e : ℕ × ℕ) :
    e ∈ joinGraphs A B f ↔ ∃ t, e ∈ bijectionGraph (f t) := by
  simp only [joinGraphs,Finset.mem_biUnion,Finset.mem_univ,true_and]

theorem joinGraphs_matching (A B : ι → Finset ℕ) (f : ∀ t, A t ≃ B t)
    (hA : Pairwise (fun s t => Disjoint (A s) (A t)))
    (hB : Pairwise (fun s t => Disjoint (B s) (B t))) : IsMatching (joinGraphs A B f) := by
  intro e he g hg h
  obtain ⟨s,hs⟩ := (mem_joinGraphs A B f e).mp he
  obtain ⟨t,ht⟩ := (mem_joinGraphs A B f g).mp hg
  by_cases hst : s=t
  · subst t; exact bijectionGraph_matching (f s) e hs g ht h
  · have hes := graph_coordinate_membership (f s) hs
    have hgt := graph_coordinate_membership (f t) ht
    rcases h with h | h
    · exact (Finset.disjoint_left.mp (hA hst) hes.1 (h ▸ hgt.1)).elim
    · exact (Finset.disjoint_left.mp (hB hst) hes.2 (h ▸ hgt.2)).elim

theorem joinGraphs_rows (A B : ι → Finset ℕ) (f : ∀ t, A t ≃ B t) :
    rows (joinGraphs A B f) = Finset.univ.biUnion A := by
  ext i
  constructor
  · intro hi
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨t,ht⟩ := (mem_joinGraphs A B f e).mp he
    exact Finset.mem_biUnion.mpr ⟨t,Finset.mem_univ _,(graph_coordinate_membership (f t) ht).1⟩
  · intro hi
    obtain ⟨t,_,hit⟩ := Finset.mem_biUnion.mp hi
    rw [← bijectionGraph_rows (f t)] at hit
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hit
    exact Finset.mem_image.mpr ⟨e,(mem_joinGraphs A B f e).mpr ⟨t,he⟩,rfl⟩

theorem joinGraphs_cols (A B : ι → Finset ℕ) (f : ∀ t, A t ≃ B t) :
    cols (joinGraphs A B f) = Finset.univ.biUnion B := by
  ext j
  constructor
  · intro hj
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨t,ht⟩ := (mem_joinGraphs A B f e).mp he
    exact Finset.mem_biUnion.mpr ⟨t,Finset.mem_univ _,(graph_coordinate_membership (f t) ht).2⟩
  · intro hj
    obtain ⟨t,_,hjt⟩ := Finset.mem_biUnion.mp hj
    rw [← bijectionGraph_cols (f t)] at hjt
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hjt
    exact Finset.mem_image.mpr ⟨e,(mem_joinGraphs A B f e).mpr ⟨t,he⟩,rfl⟩

/-- A row's unique part recovers its exact local graph from the combined graph. -/
theorem joinGraphs_restrict (A B : ι → Finset ℕ) (f : ∀ t, A t ≃ B t)
    (hA : Pairwise (fun s t => Disjoint (A s) (A t))) (t : ι) {e : ℕ × ℕ} (het : e.1 ∈ A t) :
    e ∈ joinGraphs A B f ↔ e ∈ bijectionGraph (f t) := by
  constructor
  · intro he
    obtain ⟨s,hs⟩ := (mem_joinGraphs A B f e).mp he
    by_cases hst : s=t
    · subst s; exact hs
    · exact (Finset.disjoint_left.mp (hA hst) (graph_coordinate_membership (f s) hs).1 het).elim
  · intro he; exact (mem_joinGraphs A B f e).mpr ⟨t,he⟩

theorem joinGraphs_injective (A B : ι → Finset ℕ)
    (hA : Pairwise (fun s t => Disjoint (A s) (A t))) :
    Function.Injective (joinGraphs A B) := by
  intro f g h
  funext t
  apply Equiv.ext
  intro i
  apply Subtype.ext
  have hf : ((i:ℕ),(f t i:ℕ)) ∈ joinGraphs A B f :=
    (mem_joinGraphs A B f _).mpr ⟨t,(graph_pair_mem (f t) i _).mpr rfl⟩
  rw [h] at hf
  have hg := (joinGraphs_restrict A B g hA t i.property).mp hf
  exact ((graph_pair_mem (g t) i _).mp hg).symm
/-- Agreement on the actually occupied rows preserves partial-matching containment. -/
theorem joinGraphs_subset_iff (A B : ι → Finset ℕ) (f g : ∀ t, A t ≃ B t) (P : Edges)
    (hfg : ∀ t (i : A t), (i:ℕ) ∈ rows P → f t i = g t i) :
    P ⊆ joinGraphs A B f ↔ P ⊆ joinGraphs A B g := by
  have forward : ∀ (f g : ∀ t, A t ≃ B t),
      (∀ t (i : A t), (i:ℕ) ∈ rows P → f t i = g t i) →
      P ⊆ joinGraphs A B f → P ⊆ joinGraphs A B g := by
    intro f g hfg hP e he
    obtain ⟨t,htg⟩ := (mem_joinGraphs A B f e).mp (hP he)
    obtain ⟨i,rfl⟩ := (mem_bijectionGraph (f t) e).mp htg
    have hi : (i:ℕ) ∈ rows P := Finset.mem_image.mpr ⟨_,he,rfl⟩
    apply (mem_joinGraphs A B g _).mpr
    refine ⟨t,?_⟩
    rw [graph_pair_mem,hfg t i hi]
  exact ⟨forward f g hfg,forward g f (fun t i hi => (hfg t i hi).symm)⟩
end Join

section Parts
variable {ι : Type*} [Fintype ι]

/-- Add the complement as an explicit extra part of a finite partition. -/
def partitionPart (U : Finset ℕ) (A : ι → Finset ℕ) : Option ι → Finset ℕ
  | none => U \ Finset.univ.biUnion A
  | some t => A t

theorem partitionPart_disjoint (U : Finset ℕ) (A : ι → Finset ℕ)
    (hA : Pairwise (fun s t => Disjoint (A s) (A t))) :
    Pairwise (fun s t => Disjoint (partitionPart U A s) (partitionPart U A t)) := by
  intro s t hst
  cases s with
  | none =>
    cases t with
    | none => exact (hst rfl).elim
    | some t =>
      apply Finset.disjoint_left.mpr
      intro i hi hit
      exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_biUnion.mpr ⟨t,Finset.mem_univ _,hit⟩)
  | some s =>
    cases t with
    | none =>
      apply Finset.disjoint_left.mpr
      intro i his hi
      exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_biUnion.mpr ⟨s,Finset.mem_univ _,his⟩)
    | some t => exact hA (fun h => hst (congrArg some h))

theorem partitionPart_subset (U : Finset ℕ) (A : ι → Finset ℕ)
    (hA : ∀ t, A t ⊆ U) (t : Option ι) : partitionPart U A t ⊆ U := by
  cases t with
  | none => exact Finset.sdiff_subset
  | some t => exact hA t

theorem partitionPart_cover (U : Finset ℕ) (A : ι → Finset ℕ)
    (hA : ∀ t, A t ⊆ U) : Finset.univ.biUnion (partitionPart U A) = U := by
  ext i
  constructor
  · intro hi
    obtain ⟨t,_,hit⟩ := Finset.mem_biUnion.mp hi
    exact partitionPart_subset U A hA t hit
  · intro hi
    by_cases hb : i ∈ Finset.univ.biUnion A
    · obtain ⟨t,_,hit⟩ := Finset.mem_biUnion.mp hb
      exact Finset.mem_biUnion.mpr ⟨some t,Finset.mem_univ _,hit⟩
    · exact Finset.mem_biUnion.mpr ⟨none,Finset.mem_univ _,Finset.mem_sdiff.mpr ⟨hi,hb⟩⟩
end Parts

section Actual
variable {N : ℕ} {R : Edges} (hm : IsMatching R) (hR : R ⊆ grid N N)
    (ht : chosenRewrite R = .terminal)

def rowPart : Option (Fin (chainHeight R)) → Finset ℕ :=
  partitionPart (Finset.Icc 1 N) (rowBlock hm hR ht)

def colPart : Option (Fin (chainHeight R)) → Finset ℕ :=
  partitionPart (Finset.Icc 1 N) (colBlock hm hR ht)

theorem rowPart_disjoint : Pairwise (fun s t => Disjoint (rowPart hm hR ht s) (rowPart hm hR ht t)) :=
  partitionPart_disjoint _ _ (fun _ _ hst => rowBlocks_disjoint hm hR ht hst)

theorem colPart_disjoint : Pairwise (fun s t => Disjoint (colPart hm hR ht s) (colPart hm hR ht t)) :=
  partitionPart_disjoint _ _ (fun _ _ hst => colBlocks_disjoint hm hR ht hst)

theorem rowPart_cover : Finset.univ.biUnion (rowPart hm hR ht) = Finset.Icc 1 N :=
  partitionPart_cover _ _ (rowBlock_subset hm hR ht)

theorem colPart_cover : Finset.univ.biUnion (colPart hm hR ht) = Finset.Icc 1 N :=
  partitionPart_cover _ _ (colBlock_subset hm hR ht)

theorem parts_card_eq (t : Option (Fin (chainHeight R))) :
    (rowPart hm hR ht t).card = (colPart hm hR ht t).card := by
  cases t with
  | none => exact complements_card_eq hm hR ht
  | some t => exact paired_blocks_card hm hR ht t

/-- Increasing row-to-column identification in each actual block. -/
def baseBlock (t : Fin (chainHeight R)) : rowBlock hm hR ht t ≃ colBlock hm hR ht t :=
  orderedBijection _ _ (paired_blocks_card hm hR ht t)

/-- Only the internal block permutations vary; the complement remains fixed. -/
abbrev Choices := ∀ t : Fin (chainHeight R), Equiv.Perm (rowBlock hm hR ht t)

def selectedBijection (σ : Choices hm hR ht) :
    ∀ t, rowPart hm hR ht t ≃ colPart hm hR ht t
  | none => orderedBijection _ _ (complements_card_eq hm hR ht)
  | some t => (σ t).trans (baseBlock hm hR ht t)

def blockPermutation (σ : Choices hm hR ht) : Edges :=
  joinGraphs (rowPart hm hR ht) (colPart hm hR ht) (selectedBijection hm hR ht σ)

theorem blockPermutation_matching (σ : Choices hm hR ht) : IsMatching (blockPermutation hm hR ht σ) :=
  joinGraphs_matching _ _ _ (rowPart_disjoint hm hR ht) (colPart_disjoint hm hR ht)

theorem blockPermutation_rows (σ : Choices hm hR ht) :
    rows (blockPermutation hm hR ht σ) = Finset.Icc 1 N := by
  rw [blockPermutation,joinGraphs_rows,rowPart_cover]

theorem blockPermutation_cols (σ : Choices hm hR ht) :
    cols (blockPermutation hm hR ht σ) = Finset.Icc 1 N := by
  rw [blockPermutation,joinGraphs_cols,colPart_cover]

theorem blockPermutation_grid (σ : Choices hm hR ht) : blockPermutation hm hR ht σ ⊆ grid N N := by
  intro e he
  obtain ⟨t,htg⟩ := (mem_joinGraphs _ _ _ e).mp he
  have hb := graph_coordinate_membership (selectedBijection hm hR ht σ t) htg
  apply Finset.mem_product.mpr
  exact ⟨partitionPart_subset _ _ (rowBlock_subset hm hR ht) t hb.1,
    partitionPart_subset _ _ (colBlock_subset hm hR ht) t hb.2⟩

/-- No two distinct internal block choices give the same actual global permutation. -/
theorem blockPermutation_injective : Function.Injective (blockPermutation hm hR ht) := by
  intro σ τ h
  have hh := joinGraphs_injective _ _ (rowPart_disjoint hm hR ht) h
  funext t
  apply Equiv.ext
  intro i
  apply (baseBlock hm hR ht t).injective
  have he := congrFun hh (some t)
  exact congrArg (fun f => f i) he

/-- Exact local containment for rows in a specified block. -/
theorem blockPermutation_at_block (σ : Choices hm hR ht) (t : Fin (chainHeight R))
    (i : rowBlock hm hR ht t) (j : ℕ) :
    ((i:ℕ),j) ∈ blockPermutation hm hR ht σ ↔ (baseBlock hm hR ht t (σ t i):ℕ) = j := by
  rw [blockPermutation,joinGraphs_restrict _ _ _ (rowPart_disjoint hm hR ht) (some t) (e:=((i:ℕ),j)) i.property]
  exact graph_pair_mem _ i j

/-- Exact local containment on the fixed complement. -/
theorem blockPermutation_at_complement (σ : Choices hm hR ht) (i : rowPart hm hR ht none) (j : ℕ) :
    ((i:ℕ),j) ∈ blockPermutation hm hR ht σ ↔
      (orderedBijection _ _ (complements_card_eq hm hR ht) i:ℕ) = j := by
  rw [blockPermutation,joinGraphs_restrict _ _ _ (rowPart_disjoint hm hR ht) none (e:=((i:ℕ),j)) i.property]
  exact graph_pair_mem _ i j

/-- A fully constructed choice exists for every terminal square matching. -/
def identityChoice : Choices hm hR ht := fun _ => Equiv.refl _

include hm hR ht in
theorem actual_permutation_exists : ∃ π : Edges, IsMatching π ∧ π ⊆ grid N N ∧
    rows π = Finset.Icc 1 N ∧ cols π = Finset.Icc 1 N :=
  ⟨blockPermutation hm hR ht (identityChoice hm hR ht),blockPermutation_matching hm hR ht _,
    blockPermutation_grid hm hR ht _,blockPermutation_rows hm hR ht _,blockPermutation_cols hm hR ht _⟩

/-- Actual integer weight and moment, with no unspecified evaluation functional. -/
noncomputable def blockWeight (σ : Choices hm hR ht) : ℤ :=
  ∏ t, (Equiv.Perm.sign (σ t):ℤ)

noncomputable def blockMoment (P : Edges) : ℤ :=
  ∑ σ : Choices hm hR ht, blockWeight hm hR ht σ * permutationEval (blockPermutation hm hR ht σ) P

theorem identityChoice_weight : blockWeight hm hR ht (identityChoice hm hR ht) = 1 := by
  simp [blockWeight,identityChoice,Equiv.Perm.sign_refl]

theorem actual_evaluation_expansion (σ : Choices hm hR ht) (P : Edges)
    (hP : IsMatching P) (hPg : P ⊆ grid N N) :
    permutationEval (blockPermutation hm hR ht σ) P =
      ∑ T ∈ SelfContainedCycle046.terminalFamily N N,
        SelfContainedCycle046.leafCoeff N N P T * permutationEval (blockPermutation hm hR ht σ) T :=
  SelfContainedCycle046.leafCoeff_evaluation (blockPermutation_matching hm hR ht σ)
    (blockPermutation_grid hm hR ht σ) (blockPermutation_rows hm hR ht σ)
    (blockPermutation_cols hm hR ht σ) P hP hPg
/-- The concrete global containment map respects agreement on used block rows. -/
theorem blockPermutation_subset_iff (σ τ : Choices hm hR ht) (P : Edges)
    (hστ : ∀ t (i : rowBlock hm hR ht t), (i:ℕ) ∈ rows P → σ t i = τ t i) :
    P ⊆ blockPermutation hm hR ht σ ↔ P ⊆ blockPermutation hm hR ht τ := by
  apply joinGraphs_subset_iff
  intro t i hi
  cases t with
  | none => rfl
  | some t => exact congrArg (baseBlock hm hR ht t) (hστ t i hi)

/-- Exchange the images of two chosen rows in a single block. -/
def swapChoice (t : Fin (chainHeight R)) (a b : rowBlock hm hR ht t) (σ : Choices hm hR ht) :
    Choices hm hR ht := Function.update σ t ((Equiv.swap a b).trans (σ t))

theorem swapChoice_involution (t : Fin (chainHeight R)) (a b : rowBlock hm hR ht t)
    (σ : Choices hm hR ht) : swapChoice hm hR ht t a b (swapChoice hm hR ht t a b σ) = σ := by
  funext s
  by_cases hst : s=t
  · subst s
    apply Equiv.ext
    intro i
    simp [swapChoice,Equiv.trans_apply]
  · simp [swapChoice,Function.update_of_ne hst]

theorem swapChoice_ne_self (t : Fin (chainHeight R)) (a b : rowBlock hm hR ht t)
    (hab : a ≠ b) (σ : Choices hm hR ht) : swapChoice hm hR ht t a b σ ≠ σ := by
  intro h
  have hi := congrArg (fun τ : Choices hm hR ht => τ t a) h
  simp only [swapChoice,Function.update_self,Equiv.trans_apply,Equiv.swap_apply_left] at hi
  exact hab ((σ t).injective hi).symm

/-- The actual product of block signs changes by exactly a factor -1. -/
theorem swapChoice_weight (t : Fin (chainHeight R)) (a b : rowBlock hm hR ht t)
    (hab : a ≠ b) (σ : Choices hm hR ht) :
    blockWeight hm hR ht (swapChoice hm hR ht t a b σ) = -blockWeight hm hR ht σ := by
  have hf : ∀ s, (Equiv.Perm.sign (swapChoice hm hR ht t a b σ s):ℤ) =
      (if s=t then -1 else 1) * (Equiv.Perm.sign (σ s):ℤ) := by
    intro s
    by_cases hst : s=t
    · subst s
      simp [swapChoice,Equiv.Perm.sign_trans,Equiv.Perm.sign_swap hab]
    · simp [swapChoice,hst]
  unfold blockWeight
  simp_rw [hf]
  rw [Finset.prod_mul_distrib]
  simp

/-- Swapping two rows absent from P preserves its evaluation at the actual permutation. -/
theorem swapChoice_evaluation (t : Fin (chainHeight R)) (a b : rowBlock hm hR ht t)
    (P : Edges) (ha : (a:ℕ) ∉ rows P) (hb : (b:ℕ) ∉ rows P) (σ : Choices hm hR ht) :
    permutationEval (blockPermutation hm hR ht (swapChoice hm hR ht t a b σ)) P =
      permutationEval (blockPermutation hm hR ht σ) P := by
  have he := blockPermutation_subset_iff hm hR ht (swapChoice hm hR ht t a b σ) σ P (by
    intro s i hi
    by_cases hst : s=t
    · subst s
      have hia : i ≠ a := fun h => ha (h ▸ hi)
      have hib : i ≠ b := fun h => hb (h ▸ hi)
      simp [swapChoice,Equiv.trans_apply,Equiv.swap_apply_of_ne_of_ne hia hib]
    · simp [swapChoice,Function.update_of_ne hst])
  simp only [permutationEval,he]

/-- Genuine integral cancellation on the constructed permutation family. -/
theorem blockMoment_zero_of_two_unused (t : Fin (chainHeight R))
    (a b : rowBlock hm hR ht t) (hab : a ≠ b) (P : Edges)
    (ha : (a:ℕ) ∉ rows P) (hb : (b:ℕ) ∉ rows P) : blockMoment hm hR ht P = 0 := by
  classical
  unfold blockMoment
  apply Finset.sum_involution (fun σ _ => swapChoice hm hR ht t a b σ)
  · intro σ _
    rw [swapChoice_weight hm hR ht t a b hab σ,swapChoice_evaluation hm hR ht t a b P ha hb σ]
    ring
  · intro σ _ _
    exact swapChoice_ne_self hm hR ht t a b hab σ
  · intro σ _; exact Finset.mem_univ _
  · intro σ _; exact swapChoice_involution hm hR ht t a b σ
/-- Counting the disjoint actual row blocks forces an underfilled block below degree |R|. -/
theorem exists_two_unused_block (P : Edges) (hP : P.card < R.card) :
    ∃ t : Fin (chainHeight R), 1 < (rowBlock hm hR ht t \ rows P).card := by
  by_contra hn
  push_neg at hn
  have hlevel : ∀ t : Fin (chainHeight R),
      (heightLevel R (t.val+1)).card ≤ (rowBlock hm hR ht t ∩ rows P).card := by
    intro t
    have hc := Finset.card_sdiff_add_card_inter (rowBlock hm hR ht t) (rows P)
    rw [rowBlock_card] at hc
    have h := hn t
    omega
  have hsum := Finset.sum_le_sum (fun t (_ : t ∈ (Finset.univ : Finset (Fin (chainHeight R)))) => hlevel t)
  rw [levels_total_card] at hsum
  have hd : ((Finset.univ : Finset (Fin (chainHeight R))) : Set (Fin (chainHeight R))).PairwiseDisjoint
      (fun t => rowBlock hm hR ht t ∩ rows P) := by
    intro s _ t _ hst
    exact (rowBlocks_disjoint hm hR ht hst).mono Finset.inter_subset_left Finset.inter_subset_left
  rw [← Finset.card_biUnion hd] at hsum
  have hsub : Finset.univ.biUnion (fun t => rowBlock hm hR ht t ∩ rows P) ⊆ rows P := by
    intro i hi
    obtain ⟨t,_,hit⟩ := Finset.mem_biUnion.mp hi
    exact (Finset.mem_inter.mp hit).2
  have hb := (hsum.trans (Finset.card_le_card hsub)).trans (Finset.card_image_le (s:=P) (f:=Prod.fst))
  omega

/-- All moments below the matching degree vanish for the constructed signed permutation sum. -/
theorem blockMoment_below_degree (P : Edges) (hP : P.card < R.card) : blockMoment hm hR ht P = 0 := by
  obtain ⟨t,htwo⟩ := exists_two_unused_block hm hR ht P hP
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp htwo
  have ha' := Finset.mem_sdiff.mp ha
  have hb' := Finset.mem_sdiff.mp hb
  exact blockMoment_zero_of_two_unused hm hR ht t ⟨a,ha'.1⟩ ⟨b,hb'.1⟩
    (fun h => hab (congrArg Subtype.val h)) P ha'.2 hb'.2

/-- Formal compatibility of the actual signed sum with the already constructed full reduction. -/
theorem blockMoment_reduction (P : Edges) (hP : IsMatching P) (hPg : P ⊆ grid N N) :
    blockMoment hm hR ht P = ∑ T ∈ SelfContainedCycle046.terminalFamily N N,
      SelfContainedCycle046.leafCoeff N N P T * blockMoment hm hR ht T := by
  classical
  unfold blockMoment
  simp_rw [actual_evaluation_expansion hm hR ht _ P hP hPg,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  apply Finset.sum_congr rfl
  intro σ _
  ring
theorem blockPermutation_card (σ : Choices hm hR ht) : (blockPermutation hm hR ht σ).card = N := by
  rw [← matching_rows_card (blockPermutation_matching hm hR ht σ),blockPermutation_rows]
  simp

/-- The global permutation graphs preserve the exact choice index, including at full support. -/
theorem permutation_subset_iff (σ τ : Choices hm hR ht) :
    blockPermutation hm hR ht σ ⊆ blockPermutation hm hR ht τ ↔ σ=τ := by
  constructor
  · intro h
    apply blockPermutation_injective hm hR ht
    apply Finset.eq_of_subset_of_card_le h
    rw [blockPermutation_card,blockPermutation_card]
  · intro h; subst τ; exact Finset.Subset.refl _

theorem full_permutation_evaluation (σ τ : Choices hm hR ht) :
    permutationEval (blockPermutation hm hR ht τ) (blockPermutation hm hR ht σ) =
      if σ=τ then 1 else 0 := by
  simp only [permutationEval,permutation_subset_iff]

/-- No hidden multiplicity: the full-permutation moment is exactly its single choice weight. -/
theorem blockMoment_full_permutation (σ : Choices hm hR ht) :
    blockMoment hm hR ht (blockPermutation hm hR ht σ) = blockWeight hm hR ht σ := by
  classical
  unfold blockMoment
  simp_rw [full_permutation_evaluation]
  simp

theorem blockWeight_nonzero (σ : Choices hm hR ht) : blockWeight hm hR ht σ ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro t _
  exact Units.ne_zero (Equiv.Perm.sign (σ t))

/-- Uniform non-vacuity of the constructed functional, even when R is empty. -/
theorem blockMoment_identity_full :
    blockMoment hm hR ht (blockPermutation hm hR ht (identityChoice hm hR ht)) = 1 := by
  rw [blockMoment_full_permutation,identityChoice_weight]

theorem blockMoment_swapped_full (t : Fin (chainHeight R)) (a b : rowBlock hm hR ht t)
    (hab : a ≠ b) :
    blockMoment hm hR ht (blockPermutation hm hR ht
      (swapChoice hm hR ht t a b (identityChoice hm hR ht))) = -1 := by
  rw [blockMoment_full_permutation,swapChoice_weight hm hR ht t a b hab,identityChoice_weight]

/-- Integer cancellation transports to every commutative ring, including characteristic two. -/
theorem blockMoment_below_degree_cast {F : Type*} [CommRing F] (P : Edges) (hP : P.card < R.card) :
    (∑ σ : Choices hm hR ht, (blockWeight hm hR ht σ:F) *
      (permutationEval (blockPermutation hm hR ht σ) P:F)) = 0 := by
  have h := congrArg (fun z : ℤ => (z:F)) (blockMoment_below_degree hm hR ht P hP)
  simpa only [blockMoment,Int.cast_sum,Int.cast_mul,Int.cast_zero] using h

/-- A concrete two-row block supplies real cancellation and signed nonzero full moments. -/
theorem two_by_two_signed_nonvacuity :
    ∃ (hm : IsMatching {(2,2)}) (hR : {(2,2)} ⊆ grid 2 2)
      (ht : chosenRewrite {(2,2)} = .terminal),
      blockMoment hm hR ht ∅ = 0 ∧
      (∃ σ : Choices hm hR ht, blockMoment hm hR ht (blockPermutation hm hR ht σ) = 1) ∧
      (∃ τ : Choices hm hR ht, blockMoment hm hR ht (blockPermutation hm hR ht τ) = -1) := by
  let hm : IsMatching {(2,2)} := by decide
  let hR : {(2,2)} ⊆ grid 2 2 := by decide
  let ht : chosenRewrite {(2,2)} = .terminal := by decide
  let t : Fin (chainHeight {(2,2)}) := ⟨0,by decide⟩
  have hblock : 1 < (rowBlock hm hR ht t).card := by
    rw [rowBlock_card]
    decide
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp hblock
  let a' : rowBlock hm hR ht t := ⟨a,ha⟩
  let b' : rowBlock hm hR ht t := ⟨b,hb⟩
  have hab' : a' ≠ b' := fun h => hab (congrArg Subtype.val h)
  refine ⟨hm,hR,ht,blockMoment_below_degree hm hR ht ∅ (by decide),?_,?_⟩
  · exact ⟨identityChoice hm hR ht,blockMoment_identity_full hm hR ht⟩
  · exact ⟨swapChoice hm hR ht t a' b' (identityChoice hm hR ht),
      blockMoment_swapped_full hm hR ht t a' b' hab'⟩
end Actual

end SelfContainedCycle048
