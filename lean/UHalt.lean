/-
Claude, 27 Sep 2026.  Undecidability, part C2: the switch, direction (ii), and the eventual
degree bound in the halting case (manuscript `lem:switch` (ii),(iii)).

Let the run of `M` first halt at time `T`.  The *local* argument works in any partial structure
that satisfies every clause instance of `θ_M` whose function applications are defined
(`LocSat`), provided the following are defined and lie in the domain:

    o, e,  a_j = S^j(o) (j ≤ T),  C_r(a_j),  S(C_r(a_j)) (j ≤ T, r < K),

and the domain contains `T + 1` distinct elements.  Then:

1. no `a_j` with `j < T` equals `e` (otherwise the domain would be `{a_0, …, a_j}`, too small);
2. by induction on `j ≤ T`, `Q_{state j}(a_j)` and `C_r(a_j) = a_{counter r j}`;
3. at `j = T` the state is halting, which a clause forbids.

No well-ordering, induction axiom or compactness is used: only finitely many clause instances.

Consequences:
* `no_large_model`: `θ_M` has no model on any type with `T + 1` distinct elements (finite or
  infinite);
* `theta_eventually_bounded`: for every `n ≥ T + 1` the translation of `θ_M` at size `n` has an NS
  refutation of degree `C_M`, independent of `n`, via the finite-term certificate `UHerbrand`.
-/
import USwitch
import UHerbrand

set_option autoImplicit false
set_option linter.unusedSimpArgs false
open MvPolynomial DegreeProfilesReview.NS

namespace ClaudeUndec

/-! ### Atoms of `θ_M` in partial structures -/

section HoldsP
variable (P : Prog) {U : Type} (S : PStr U) (σ : ℕ → U)

theorem holdsP_ltA (i j : ℕ) : atomHoldsP (theta P) S σ (ltA i j) ↔ S.rel 0 [σ i, σ j] := by
  simp only [ltA, atomHoldsP, Sentence.rels, theta, thRels_getD_zero, thRels_length]
  simp

theorem holdsP_qA {ℓ : ℕ} (h : ℓ ≤ P.length) (i : ℕ) :
    atomHoldsP (theta P) S σ (qA ℓ i) ↔ S.rel (1 + ℓ) [σ i] := by
  simp only [qA, atomHoldsP, Sentence.rels, theta, thRels_getD_q P h, thRels_length]
  simp only [List.length_singleton, List.map_cons, List.map_nil, true_and]
  constructor
  · exact fun h => h.2
  · exact fun h' => ⟨by omega, h'⟩

theorem holdsP_isO (u : ℕ) : atomHoldsP (theta P) S σ (isO u) ↔ S.fn 0 [] = some (σ u) := by
  simp only [isO, atomHoldsP, Sentence.funs, theta, thFuns_getD_o, thFuns_length]
  simp

theorem holdsP_isE (u : ℕ) : atomHoldsP (theta P) S σ (isE u) ↔ S.fn 1 [] = some (σ u) := by
  simp only [isE, atomHoldsP, Sentence.funs, theta, thFuns_getD_e, thFuns_length]
  simp

theorem holdsP_sOf (v t : ℕ) :
    atomHoldsP (theta P) S σ (sOf v t) ↔ S.fn 2 [σ t] = some (σ v) := by
  simp only [sOf, atomHoldsP, Sentence.funs, theta, thFuns_getD_S, thFuns_length]
  simp

theorem holdsP_cOf {r : ℕ} (hr : r < P.ncnt) (c t : ℕ) :
    atomHoldsP (theta P) S σ (cOf r c t) ↔ S.fn (3 + r) [σ t] = some (σ c) := by
  simp only [cOf, atomHoldsP, Sentence.funs, theta, thFuns_getD_C P hr, thFuns_length]
  simp only [List.length_singleton, List.map_cons, List.map_nil, true_and]
  constructor
  · exact fun h => h.2
  · exact fun h' => ⟨by omega, h'⟩

theorem holdsP_eq (i j : ℕ) : atomHoldsP (theta P) S σ (Atom.eq i j) ↔ σ i = σ j := Iff.rfl

theorem litHoldsP_pos (a : Atom) :
    litHoldsP (theta P) S σ (pos a) ↔ atomHoldsP (theta P) S σ a := by
  simp [litHoldsP, pos]

theorem litHoldsP_neg (a : Atom) :
    litHoldsP (theta P) S σ (neg a) ↔ ¬ atomHoldsP (theta P) S σ a := by
  simp [litHoldsP, neg]

theorem existsP_cons (l : Lit) (c : Clause) :
    (∃ l' ∈ l :: c, litHoldsP (theta P) S σ l') ↔
      litHoldsP (theta P) S σ l ∨ ∃ l' ∈ c, litHoldsP (theta P) S σ l' := by
  simp

theorem existsP_nil : ¬ ∃ l' ∈ ([] : Clause), litHoldsP (theta P) S σ l' := by simp

theorem existsP_append (c c' : Clause) :
    (∃ l' ∈ c ++ c', litHoldsP (theta P) S σ l') ↔
      (∃ l' ∈ c, litHoldsP (theta P) S σ l') ∨ ∃ l' ∈ c', litHoldsP (theta P) S σ l' := by
  simp [or_and_right, exists_or]

theorem defined_isO (u : ℕ) : Defined S σ (isO u) ↔ ∃ y, S.fn 0 [] = some y := Iff.rfl
theorem defined_isE (u : ℕ) : Defined S σ (isE u) ↔ ∃ y, S.fn 1 [] = some y := Iff.rfl
theorem defined_sOf (v t : ℕ) : Defined S σ (sOf v t) ↔ ∃ y, S.fn 2 [σ t] = some y := Iff.rfl
theorem defined_cOf (r c t : ℕ) : Defined S σ (cOf r c t) ↔ ∃ y, S.fn (3 + r) [σ t] = some y :=
  Iff.rfl
theorem defined_ltA (i j : ℕ) : Defined S σ (ltA i j) := trivial
theorem defined_qA (ℓ i : ℕ) : Defined S σ (qA ℓ i) := trivial
theorem defined_eq (i j : ℕ) : Defined S σ (Atom.eq i j) := trivial

end HoldsP

/-- A clause-variable assignment given by eight values. -/
def inst8 {U : Type} (x0 x1 x2 x3 x4 x5 x6 x7 : U) : ℕ → U
  | 0 => x0 | 1 => x1 | 2 => x2 | 3 => x3 | 4 => x4 | 5 => x5 | 6 => x6 | 7 => x7 | _ => x0

theorem inst8_dom {U : Type} (p : U → Prop) {x0 x1 x2 x3 x4 x5 x6 x7 : U} (h0 : p x0)
    (h1 : p x1) (h2 : p x2) (h3 : p x3) (h4 : p x4) (h5 : p x5) (h6 : p x6) (h7 : p x7) :
    ∀ v, p (inst8 x0 x1 x2 x3 x4 x5 x6 x7 v)
  | 0 => h0 | 1 => h1 | 2 => h2 | 3 => h3 | 4 => h4 | 5 => h5 | 6 => h6 | 7 => h7
  | _ + 8 => h0

/-! ### Clause membership -/

section Mem
variable (P : Prog)

theorem mem_base {c : Clause} (h : c ∈ baseClauses P) : c ∈ (theta P).clauses :=
  List.mem_append_left _ h

theorem mem_trans {ℓ : ℕ} (hℓ : ℓ < P.length) {i : Instr} (hi : P[ℓ]? = some i) {c : Clause}
    (h : c ∈ transClauses P ℓ i) : c ∈ (theta P).clauses := by
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨ℓ, List.mem_range.mpr hℓ, ?_⟩)
  rw [hi]; exact h

theorem mem_same {ℓ r r' : ℕ} (extra : Clause) (hr' : r' < P.ncnt) (hne : r' ≠ r) :
    pre ℓ ++ extra ++ [neg (cOf r' 6 0), pos (cOf r' 6 2)] ∈ sameClauses P ℓ r extra :=
  List.mem_map.mpr ⟨r', List.mem_filter.mpr ⟨List.mem_range.mpr hr', by simpa using hne⟩, rfl⟩

end Mem

/-! ### Clause instances used by the local argument -/

section Facts
variable (P : Prog) {U : Type} (S : PStr U) (hS : LocSat (theta P) S)
include hS

theorem F_irrefl {x : U} (hx : S.dom x) : ¬ S.rel 0 [x, x] := by
  have h := hS _ (mem_base P (c := [neg (ltA 0 0)]) (by simp [baseClauses]))
    (inst8 x x x x x x x x) (fun v _ => inst8_dom S.dom hx hx hx hx hx hx hx hx v)
    (by simp only [List.forall_mem_cons, neg, pos, defined_ltA, List.not_mem_nil, false_imp_iff,
      implies_true, and_true])
  simpa only [existsP_cons, existsP_nil, or_false, litHoldsP_neg, holdsP_ltA, inst8] using h

theorem F_trans {x y z : U} (hx : S.dom x) (hy : S.dom y) (hz : S.dom z)
    (h1 : S.rel 0 [x, z]) (h2 : S.rel 0 [z, y]) : S.rel 0 [x, y] := by
  have h := hS _ (mem_base P (c := [neg (ltA 0 7), neg (ltA 7 2), pos (ltA 0 2)])
    (by simp [baseClauses]))
    (inst8 x x y x x x x z) (fun v _ => inst8_dom S.dom hx hx hy hx hx hx hx hz v)
    (by simp only [List.forall_mem_cons, neg, pos, defined_ltA, List.not_mem_nil, false_imp_iff,
      implies_true, and_true])
  simp only [existsP_cons, existsP_nil, or_false, litHoldsP_neg, litHoldsP_pos, holdsP_ltA,
    inst8] at h
  tauto

theorem F_lin {x y : U} (hx : S.dom x) (hy : S.dom y) :
    S.rel 0 [x, y] ∨ x = y ∨ S.rel 0 [y, x] := by
  have h := hS _ (mem_base P (c := [pos (ltA 0 2), pos (Atom.eq 0 2), pos (ltA 2 0)])
    (by simp [baseClauses]))
    (inst8 x x y x x x x x) (fun v _ => inst8_dom S.dom hx hx hy hx hx hx hx hx v)
    (by simp only [List.forall_mem_cons, neg, pos, defined_ltA, defined_eq, List.not_mem_nil,
      false_imp_iff, implies_true, and_true, true_and, inst8])
  simpa only [existsP_cons, existsP_nil, or_false, litHoldsP_neg, litHoldsP_pos, holdsP_ltA,
    holdsP_eq, inst8] using h

theorem F_least {o x : U} (ho : S.fn 0 [] = some o) (hod : S.dom o) (hx : S.dom x) :
    x = o ∨ S.rel 0 [o, x] := by
  have h := hS _ (mem_base P (c := [neg (isO 1), pos (Atom.eq 0 1), pos (ltA 1 0)])
    (by simp [baseClauses]))
    (inst8 x o x x x x x x) (fun v _ => inst8_dom S.dom hx hod hx hx hx hx hx hx v)
    (by simp only [List.forall_mem_cons, neg, pos, defined_ltA, defined_eq, defined_isO,
      List.not_mem_nil, false_imp_iff, implies_true, and_true, true_and, inst8]; exact ⟨_, ho⟩)
  simp only [existsP_cons, existsP_nil, or_false, litHoldsP_neg, litHoldsP_pos, holdsP_ltA,
    holdsP_eq, holdsP_isO, inst8] at h
  tauto

theorem F_greatest {e x : U} (he : S.fn 1 [] = some e) (hed : S.dom e) (hx : S.dom x) :
    x = e ∨ S.rel 0 [x, e] := by
  have h := hS _ (mem_base P (c := [neg (isE 1), pos (Atom.eq 0 1), pos (ltA 0 1)])
    (by simp [baseClauses]))
    (inst8 x e x x x x x x) (fun v _ => inst8_dom S.dom hx hed hx hx hx hx hx hx v)
    (by simp only [List.forall_mem_cons, neg, pos, defined_ltA, defined_eq, defined_isE,
      List.not_mem_nil, false_imp_iff, implies_true, and_true, true_and, inst8]; exact ⟨_, he⟩)
  simp only [existsP_cons, existsP_nil, or_false, litHoldsP_neg, litHoldsP_pos, holdsP_ltA,
    holdsP_eq, holdsP_isE, inst8] at h
  tauto

theorem F_succ {e t s : U} (he : S.fn 1 [] = some e) (hed : S.dom e) (htd : S.dom t)
    (hsd : S.dom s) (hts : S.fn 2 [t] = some s) (hne : t ≠ e) : S.rel 0 [t, s] := by
  have h := hS _ (mem_base P (c := [neg (isE 1), pos (Atom.eq 0 1), neg (sOf 2 0), pos (ltA 0 2)])
    (by simp [baseClauses]))
    (inst8 t e s t t t t t) (fun v _ => inst8_dom S.dom htd hed hsd htd htd htd htd htd v)
    (by simp only [List.forall_mem_cons, neg, pos, defined_ltA, defined_eq, defined_isE,
      defined_sOf, List.not_mem_nil, false_imp_iff, implies_true, and_true, true_and, inst8]
        exact ⟨⟨_, he⟩, ⟨_, hts⟩⟩)
  simp only [existsP_cons, existsP_nil, or_false, litHoldsP_neg, litHoldsP_pos, holdsP_ltA,
    holdsP_eq, holdsP_isE, holdsP_sOf, inst8] at h
  tauto

theorem F_imm {e t s z : U} (he : S.fn 1 [] = some e) (hed : S.dom e) (htd : S.dom t)
    (hsd : S.dom s) (hzd : S.dom z) (hts : S.fn 2 [t] = some s) (hne : t ≠ e)
    (h1 : S.rel 0 [t, z]) (h2 : S.rel 0 [z, s]) : False := by
  have h := hS _ (mem_base P (c := [neg (isE 1), pos (Atom.eq 0 1), neg (sOf 2 0),
      neg (ltA 0 7), neg (ltA 7 2)]) (by simp [baseClauses]))
    (inst8 t e s t t t t z) (fun v _ => inst8_dom S.dom htd hed hsd htd htd htd htd hzd v)
    (by simp only [List.forall_mem_cons, neg, pos, defined_ltA, defined_eq, defined_isE,
      defined_sOf, List.not_mem_nil, false_imp_iff, implies_true, and_true, true_and, inst8]
        exact ⟨⟨_, he⟩, ⟨_, hts⟩⟩)
  simp only [existsP_cons, existsP_nil, or_false, litHoldsP_neg, litHoldsP_pos, holdsP_ltA,
    holdsP_eq, holdsP_isE, holdsP_sOf, inst8] at h
  tauto

theorem F_q0 {o : U} (ho : S.fn 0 [] = some o) (hod : S.dom o) : S.rel (1 + 0) [o] := by
  have h := hS _ (mem_base P (c := [neg (isO 1), pos (qA 0 1)]) (by simp [baseClauses]))
    (inst8 o o o o o o o o) (fun v _ => inst8_dom S.dom hod hod hod hod hod hod hod hod v)
    (by simp only [List.forall_mem_cons, neg, pos, defined_qA, defined_isO,
      List.not_mem_nil, false_imp_iff, implies_true, and_true, true_and, inst8]; exact ⟨_, ho⟩)
  simp only [existsP_cons, existsP_nil, or_false, litHoldsP_neg, litHoldsP_pos,
    holdsP_qA P S _ (Nat.zero_le _), holdsP_isO, inst8] at h
  tauto

theorem F_c0 {o c : U} {r : ℕ} (hr : r < P.ncnt) (ho : S.fn 0 [] = some o) (hod : S.dom o)
    (hcd : S.dom c) (hc : S.fn (3 + r) [o] = some c) : c = o := by
  have h := hS _ (mem_base P (c := [neg (isO 1), neg (cOf r 3 1), pos (Atom.eq 3 1)])
    (by simp only [baseClauses, List.mem_append, List.mem_map, List.mem_range]
        exact Or.inl (Or.inr ⟨r, hr, rfl⟩)))
    (inst8 o o o c o o o o) (fun v _ => inst8_dom S.dom hod hod hod hcd hod hod hod hod v)
    (by simp only [List.forall_mem_cons, neg, pos, defined_eq, defined_isO, defined_cOf,
      List.not_mem_nil, false_imp_iff, implies_true, and_true, true_and, inst8]; exact ⟨⟨_, ho⟩, ⟨_, hc⟩⟩)
  simp only [existsP_cons, existsP_nil, or_false, litHoldsP_neg, litHoldsP_pos,
    holdsP_isO, holdsP_cOf P S _ hr, holdsP_eq, inst8] at h
  tauto

theorem F_halt {ℓ : ℕ} (hℓ : ℓ ≤ P.length) (hh : P.IsHaltSt ℓ) {x : U} (hx : S.dom x) :
    ¬ S.rel (1 + ℓ) [x] := by
  have h := hS _ (mem_base P (c := [neg (qA ℓ 0)])
    (by simp only [baseClauses, List.mem_append, List.mem_map, List.mem_filter, List.mem_range]
        exact Or.inr ⟨ℓ, ⟨by omega, decide_eq_true hh⟩, rfl⟩))
    (inst8 x x x x x x x x) (fun v _ => inst8_dom S.dom hx hx hx hx hx hx hx hx v)
    (by simp only [List.forall_mem_cons, neg, pos, defined_qA,
      List.not_mem_nil, false_imp_iff, implies_true, and_true, true_and, inst8])
  simpa only [existsP_cons, existsP_nil, or_false, litHoldsP_neg, holdsP_qA P S _ hℓ, inst8]
    using h

/-! #### Transitions -/

section Trans
variable {ℓ : ℕ} (hℓ : ℓ < P.length) {e t v : U} (he : S.fn 1 [] = some e) (hne : t ≠ e)
  (hQ : S.rel (1 + ℓ) [t]) (hv : S.fn 2 [t] = some v)
  (hed : S.dom e) (htd : S.dom t) (hvd : S.dom v)
include hℓ he hne hQ hv hed htd hvd

theorem T_inc_cnt {r ℓ' : ℕ} (hi : P[ℓ]? = some (Sum.inl (r, ℓ'))) {c w : U}
    (hcd : S.dom c) (hwd : S.dom w) (hc : S.fn (3 + r) [t] = some c) (hw : S.fn 2 [c] = some w)
    (hcv : ∃ y, S.fn (3 + r) [v] = some y) : S.fn (3 + r) [v] = some w := by
  have hr : r < P.ncnt := P.instrCnt_lt hi
  have h := hS _ (mem_trans P hℓ hi (c := pre ℓ ++ [neg (cOf r 3 0), neg (sOf 4 3),
      pos (cOf r 4 2)]) (by simp only [transClauses, List.mem_append, List.mem_cons, true_or,
        or_true]))
    (inst8 t e v c w t t t) (fun x _ => inst8_dom S.dom htd hed hvd hcd hwd htd htd htd x)
    (by simp only [pre, List.cons_append, List.nil_append, List.forall_mem_cons, neg, pos,
      defined_ltA, defined_eq, defined_isE, defined_sOf, defined_cOf, defined_qA,
      List.not_mem_nil, false_imp_iff, implies_true, and_true, true_and, inst8]
        exact ⟨⟨_, he⟩, ⟨_, hv⟩, ⟨_, hc⟩, ⟨_, hw⟩, hcv⟩)
  simp only [pre, List.cons_append, List.nil_append, existsP_cons, existsP_nil, or_false,
    litHoldsP_neg, litHoldsP_pos, holdsP_ltA, holdsP_eq, holdsP_isE, holdsP_sOf,
    holdsP_qA P S _ hℓ.le, holdsP_cOf P S _ hr, inst8] at h
  tauto

theorem T_inc_st {r ℓ' : ℕ} (hi : P[ℓ]? = some (Sum.inl (r, ℓ'))) :
    S.rel (1 + P.norm ℓ') [v] := by
  have h := hS _ (mem_trans P hℓ hi (c := pre ℓ ++ [pos (qA (P.norm ℓ') 2)])
      (by simp only [transClauses, List.mem_append, List.mem_cons, true_or, or_true]))
    (inst8 t e v t t t t t) (fun x _ => inst8_dom S.dom htd hed hvd htd htd htd htd htd x)
    (by simp only [pre, List.cons_append, List.nil_append, List.forall_mem_cons, neg, pos,
      defined_ltA, defined_eq, defined_isE, defined_sOf, defined_cOf, defined_qA,
      List.not_mem_nil, false_imp_iff, implies_true, and_true, true_and, inst8]
        exact ⟨⟨_, he⟩, ⟨_, hv⟩⟩)
  simp only [pre, List.cons_append, List.nil_append, existsP_cons, existsP_nil, or_false,
    litHoldsP_neg, litHoldsP_pos, holdsP_ltA, holdsP_eq, holdsP_isE, holdsP_sOf,
    holdsP_qA P S _ hℓ.le, holdsP_qA P S _ (P.norm_le ℓ'), inst8] at h
  tauto

theorem T_inc_same {r ℓ' r' : ℕ} (hi : P[ℓ]? = some (Sum.inl (r, ℓ'))) (hr' : r' < P.ncnt)
    (hne' : r' ≠ r) {d : U} (hdd : S.dom d) (hd : S.fn (3 + r') [t] = some d)
    (hdv : ∃ y, S.fn (3 + r') [v] = some y) : S.fn (3 + r') [v] = some d := by
  have h := hS _ (mem_trans P hℓ hi (c := pre ℓ ++ [] ++ [neg (cOf r' 6 0), pos (cOf r' 6 2)])
      (by simp only [transClauses]
          exact List.mem_append_right _ (mem_same P [] hr' hne')))
    (inst8 t e v t t t d t) (fun x _ => inst8_dom S.dom htd hed hvd htd htd htd hdd htd x)
    (by simp only [pre, List.cons_append, List.nil_append, List.append_nil, List.forall_mem_cons,
      neg, pos, defined_ltA, defined_eq, defined_isE, defined_sOf, defined_cOf, defined_qA,
      List.not_mem_nil, false_imp_iff, implies_true, and_true, true_and, inst8]
        exact ⟨⟨_, he⟩, ⟨_, hv⟩, ⟨_, hd⟩, hdv⟩)
  simp only [pre, List.cons_append, List.nil_append, List.append_nil, existsP_cons, existsP_nil,
    or_false, litHoldsP_neg, litHoldsP_pos, holdsP_ltA, holdsP_eq, holdsP_isE, holdsP_sOf,
    holdsP_qA P S _ hℓ.le, holdsP_cOf P S _ hr', inst8] at h
  tauto

variable {o : U} (ho : S.fn 0 [] = some o) (hod : S.dom o)
include ho hod

theorem T_dz_cnt {r ℓ₀ ℓ₁ : ℕ} (hi : P[ℓ]? = some (Sum.inr (Sum.inl (r, ℓ₀, ℓ₁))))
    (hc : S.fn (3 + r) [t] = some o) (hcv : ∃ y, S.fn (3 + r) [v] = some y) :
    S.fn (3 + r) [v] = some o := by
  have hr : r < P.ncnt := P.instrCnt_lt hi
  have h := hS _ (mem_trans P hℓ hi (c := pre ℓ ++ [neg (isO 5), neg (cOf r 3 0),
      neg (Atom.eq 3 5), pos (cOf r 3 2)])
      (by simp only [transClauses, List.mem_append, List.mem_cons, true_or, or_true]))
    (inst8 t e v o t o t t) (fun x _ => inst8_dom S.dom htd hed hvd hod htd hod htd htd x)
    (by simp only [pre, List.cons_append, List.nil_append, List.forall_mem_cons, neg, pos,
      defined_ltA, defined_eq, defined_isE, defined_isO, defined_sOf, defined_cOf, defined_qA,
      List.not_mem_nil, false_imp_iff, implies_true, and_true, true_and, inst8]
        exact ⟨⟨_, he⟩, ⟨_, hv⟩, ⟨_, ho⟩, ⟨_, hc⟩, hcv⟩)
  simp only [pre, List.cons_append, List.nil_append, existsP_cons, existsP_nil, or_false,
    litHoldsP_neg, litHoldsP_pos, holdsP_ltA, holdsP_eq, holdsP_isE, holdsP_isO, holdsP_sOf,
    holdsP_qA P S _ hℓ.le, holdsP_cOf P S _ hr, inst8] at h
  tauto

theorem T_dz_st {r ℓ₀ ℓ₁ : ℕ} (hi : P[ℓ]? = some (Sum.inr (Sum.inl (r, ℓ₀, ℓ₁))))
    (hc : S.fn (3 + r) [t] = some o) : S.rel (1 + P.norm ℓ₀) [v] := by
  have hr : r < P.ncnt := P.instrCnt_lt hi
  have h := hS _ (mem_trans P hℓ hi (c := pre ℓ ++ [neg (isO 5), neg (cOf r 3 0),
      neg (Atom.eq 3 5), pos (qA (P.norm ℓ₀) 2)])
      (by simp only [transClauses, List.mem_append, List.mem_cons, true_or, or_true]))
    (inst8 t e v o t o t t) (fun x _ => inst8_dom S.dom htd hed hvd hod htd hod htd htd x)
    (by simp only [pre, List.cons_append, List.nil_append, List.forall_mem_cons, neg, pos,
      defined_ltA, defined_eq, defined_isE, defined_isO, defined_sOf, defined_cOf, defined_qA,
      List.not_mem_nil, false_imp_iff, implies_true, and_true, true_and, inst8]
        exact ⟨⟨_, he⟩, ⟨_, hv⟩, ⟨_, ho⟩, ⟨_, hc⟩⟩)
  simp only [pre, List.cons_append, List.nil_append, existsP_cons, existsP_nil, or_false,
    litHoldsP_neg, litHoldsP_pos, holdsP_ltA, holdsP_eq, holdsP_isE, holdsP_isO, holdsP_sOf,
    holdsP_qA P S _ hℓ.le, holdsP_qA P S _ (P.norm_le ℓ₀), holdsP_cOf P S _ hr, inst8] at h
  tauto

theorem T_dz_same {r ℓ₀ ℓ₁ r' : ℕ} (hi : P[ℓ]? = some (Sum.inr (Sum.inl (r, ℓ₀, ℓ₁))))
    (hc : S.fn (3 + r) [t] = some o) (hr' : r' < P.ncnt) (hne' : r' ≠ r) {d : U} (hdd : S.dom d)
    (hd : S.fn (3 + r') [t] = some d) (hdv : ∃ y, S.fn (3 + r') [v] = some y) :
    S.fn (3 + r') [v] = some d := by
  have hr : r < P.ncnt := P.instrCnt_lt hi
  have h := hS _ (mem_trans P hℓ hi (c := pre ℓ ++ [neg (isO 5), neg (cOf r 3 0),
      neg (Atom.eq 3 5)] ++ [neg (cOf r' 6 0), pos (cOf r' 6 2)])
      (by simp only [transClauses]
          exact List.mem_append_left _ (List.mem_append_right _ (mem_same P _ hr' hne'))))
    (inst8 t e v o t o d t) (fun x _ => inst8_dom S.dom htd hed hvd hod htd hod hdd htd x)
    (by simp only [pre, List.cons_append, List.nil_append, List.forall_mem_cons, neg, pos,
      defined_ltA, defined_eq, defined_isE, defined_isO, defined_sOf, defined_cOf, defined_qA,
      List.not_mem_nil, false_imp_iff, implies_true, and_true, true_and, inst8]
        exact ⟨⟨_, he⟩, ⟨_, hv⟩, ⟨_, ho⟩, ⟨_, hc⟩, ⟨_, hd⟩, hdv⟩)
  simp only [pre, List.cons_append, List.nil_append, existsP_cons, existsP_nil, or_false,
    litHoldsP_neg, litHoldsP_pos, holdsP_ltA, holdsP_eq, holdsP_isE, holdsP_isO, holdsP_sOf,
    holdsP_qA P S _ hℓ.le, holdsP_cOf P S _ hr, holdsP_cOf P S _ hr', inst8] at h
  tauto

theorem T_dp_lt {r ℓ₀ ℓ₁ : ℕ} (hi : P[ℓ]? = some (Sum.inr (Sum.inl (r, ℓ₀, ℓ₁)))) {c d : U}
    (hcd : S.dom c) (hdd : S.dom d) (hc : S.fn (3 + r) [t] = some c) (hco : c ≠ o)
    (hd : S.fn (3 + r) [v] = some d) : S.rel 0 [d, c] := by
  have hr : r < P.ncnt := P.instrCnt_lt hi
  have h := hS _ (mem_trans P hℓ hi (c := pre ℓ ++ [neg (isO 5), neg (cOf r 3 0),
      pos (Atom.eq 3 5), neg (cOf r 6 2), pos (ltA 6 3)])
      (by simp only [transClauses, List.mem_append, List.mem_cons, true_or, or_true]))
    (inst8 t e v c t o d t) (fun x _ => inst8_dom S.dom htd hed hvd hcd htd hod hdd htd x)
    (by simp only [pre, List.cons_append, List.nil_append, List.forall_mem_cons, neg, pos,
      defined_ltA, defined_eq, defined_isE, defined_isO, defined_sOf, defined_cOf, defined_qA,
      List.not_mem_nil, false_imp_iff, implies_true, and_true, true_and, inst8]
        exact ⟨⟨_, he⟩, ⟨_, hv⟩, ⟨_, ho⟩, ⟨_, hc⟩, ⟨_, hd⟩⟩)
  simp only [pre, List.cons_append, List.nil_append, existsP_cons, existsP_nil, or_false,
    litHoldsP_neg, litHoldsP_pos, holdsP_ltA, holdsP_eq, holdsP_isE, holdsP_isO, holdsP_sOf,
    holdsP_qA P S _ hℓ.le, holdsP_cOf P S _ hr, inst8] at h
  tauto

theorem T_dp_s {r ℓ₀ ℓ₁ : ℕ} (hi : P[ℓ]? = some (Sum.inr (Sum.inl (r, ℓ₀, ℓ₁)))) {c d w : U}
    (hcd : S.dom c) (hdd : S.dom d) (hwd : S.dom w) (hc : S.fn (3 + r) [t] = some c)
    (hco : c ≠ o) (hd : S.fn (3 + r) [v] = some d) (hw : S.fn 2 [d] = some w) : w = c := by
  have hr : r < P.ncnt := P.instrCnt_lt hi
  have h := hS _ (mem_trans P hℓ hi (c := pre ℓ ++ [neg (isO 5), neg (cOf r 3 0),
      pos (Atom.eq 3 5), neg (cOf r 6 2), neg (sOf 4 6), pos (Atom.eq 4 3)])
      (by simp only [transClauses, List.mem_append, List.mem_cons, true_or, or_true]))
    (inst8 t e v c w o d t) (fun x _ => inst8_dom S.dom htd hed hvd hcd hwd hod hdd htd x)
    (by simp only [pre, List.cons_append, List.nil_append, List.forall_mem_cons, neg, pos,
      defined_ltA, defined_eq, defined_isE, defined_isO, defined_sOf, defined_cOf, defined_qA,
      List.not_mem_nil, false_imp_iff, implies_true, and_true, true_and, inst8]
        exact ⟨⟨_, he⟩, ⟨_, hv⟩, ⟨_, ho⟩, ⟨_, hc⟩, ⟨_, hd⟩, ⟨_, hw⟩⟩)
  simp only [pre, List.cons_append, List.nil_append, existsP_cons, existsP_nil, or_false,
    litHoldsP_neg, litHoldsP_pos, holdsP_ltA, holdsP_eq, holdsP_isE, holdsP_isO, holdsP_sOf,
    holdsP_qA P S _ hℓ.le, holdsP_cOf P S _ hr, inst8] at h
  tauto

theorem T_dp_st {r ℓ₀ ℓ₁ : ℕ} (hi : P[ℓ]? = some (Sum.inr (Sum.inl (r, ℓ₀, ℓ₁)))) {c : U}
    (hcd : S.dom c) (hc : S.fn (3 + r) [t] = some c) (hco : c ≠ o) :
    S.rel (1 + P.norm ℓ₁) [v] := by
  have hr : r < P.ncnt := P.instrCnt_lt hi
  have h := hS _ (mem_trans P hℓ hi (c := pre ℓ ++ [neg (isO 5), neg (cOf r 3 0),
      pos (Atom.eq 3 5), pos (qA (P.norm ℓ₁) 2)])
      (by simp only [transClauses, List.mem_append, List.mem_cons, true_or, or_true]))
    (inst8 t e v c t o t t) (fun x _ => inst8_dom S.dom htd hed hvd hcd htd hod htd htd x)
    (by simp only [pre, List.cons_append, List.nil_append, List.forall_mem_cons, neg, pos,
      defined_ltA, defined_eq, defined_isE, defined_isO, defined_sOf, defined_cOf, defined_qA,
      List.not_mem_nil, false_imp_iff, implies_true, and_true, true_and, inst8]
        exact ⟨⟨_, he⟩, ⟨_, hv⟩, ⟨_, ho⟩, ⟨_, hc⟩⟩)
  simp only [pre, List.cons_append, List.nil_append, existsP_cons, existsP_nil, or_false,
    litHoldsP_neg, litHoldsP_pos, holdsP_ltA, holdsP_eq, holdsP_isE, holdsP_isO, holdsP_sOf,
    holdsP_qA P S _ hℓ.le, holdsP_qA P S _ (P.norm_le ℓ₁), holdsP_cOf P S _ hr, inst8] at h
  tauto

theorem T_dp_same {r ℓ₀ ℓ₁ r' : ℕ} (hi : P[ℓ]? = some (Sum.inr (Sum.inl (r, ℓ₀, ℓ₁)))) {c : U}
    (hcd : S.dom c) (hc : S.fn (3 + r) [t] = some c) (hco : c ≠ o) (hr' : r' < P.ncnt)
    (hne' : r' ≠ r) {d : U} (hdd : S.dom d)
    (hd : S.fn (3 + r') [t] = some d) (hdv : ∃ y, S.fn (3 + r') [v] = some y) :
    S.fn (3 + r') [v] = some d := by
  have hr : r < P.ncnt := P.instrCnt_lt hi
  have h := hS _ (mem_trans P hℓ hi (c := pre ℓ ++ [neg (isO 5), neg (cOf r 3 0),
      pos (Atom.eq 3 5)] ++ [neg (cOf r' 6 0), pos (cOf r' 6 2)])
      (by simp only [transClauses]
          exact List.mem_append_right _ (mem_same P _ hr' hne')))
    (inst8 t e v c t o d t) (fun x _ => inst8_dom S.dom htd hed hvd hcd htd hod hdd htd x)
    (by simp only [pre, List.cons_append, List.nil_append, List.forall_mem_cons, neg, pos,
      defined_ltA, defined_eq, defined_isE, defined_isO, defined_sOf, defined_cOf, defined_qA,
      List.not_mem_nil, false_imp_iff, implies_true, and_true, true_and, inst8]
        exact ⟨⟨_, he⟩, ⟨_, hv⟩, ⟨_, ho⟩, ⟨_, hc⟩, ⟨_, hd⟩, hdv⟩)
  simp only [pre, List.cons_append, List.nil_append, existsP_cons, existsP_nil, or_false,
    litHoldsP_neg, litHoldsP_pos, holdsP_ltA, holdsP_eq, holdsP_isE, holdsP_isO, holdsP_sOf,
    holdsP_qA P S _ hℓ.le, holdsP_cOf P S _ hr, holdsP_cOf P S _ hr', inst8] at h
  tauto

end Trans

end Facts

theorem Prog.halt_norm (P : Prog) {ℓ : ℕ} (hh : P.IsHaltSt ℓ) : P.IsHaltSt (P.norm ℓ) := by
  unfold Prog.norm
  rcases hh with h | h
  · left; omega
  · have hl : ℓ < P.length := by
      by_contra hc
      rw [List.getElem?_eq_none (by omega)] at h
      cases h
    right
    rw [min_eq_left hl.le]; exact h

/-! ### The local argument -/

section Local
variable (P : Prog) {U : Type} (S : PStr U) (hS : LocSat (theta P) S) {T : ℕ}
  (hT' : ∀ j < T, ¬ P.IsHaltSt (P.cfg j).1)
  (a : ℕ → U) (e : U) (cv sv : ℕ → ℕ → U)
  (ho : S.fn 0 [] = some (a 0)) (he : S.fn 1 [] = some e)
  (ha : ∀ j < T, S.fn 2 [a j] = some (a (j + 1)))
  (hc : ∀ j ≤ T, ∀ r < P.ncnt, S.fn (3 + r) [a j] = some (cv r j))
  (hs : ∀ j ≤ T, ∀ r < P.ncnt, S.fn 2 [cv r j] = some (sv r j))
  (hda : ∀ j ≤ T, S.dom (a j)) (hde : S.dom e)
  (hdc : ∀ j ≤ T, ∀ r < P.ncnt, S.dom (cv r j)) (hds : ∀ j ≤ T, ∀ r < P.ncnt, S.dom (sv r j))
  (d : Fin (T + 1) → U) (hd : Function.Injective d) (hdd : ∀ i, S.dom (d i))

include hS ho he ha hda hde hd hdd in
/-- Step 1: the chain `a_0, a_1, …` does not reach `e` before time `T`, because the domain has
`T + 1` distinct elements. -/
theorem no_early_e : ∀ j < T, a j ≠ e := by
  classical
  by_contra hcon
  push_neg at hcon
  have hj0 : Nat.find hcon < T ∧ a (Nat.find hcon) = e := Nat.find_spec hcon
  have hmin : ∀ i < Nat.find hcon, a i ≠ e :=
    fun i hi hai => Nat.find_min hcon hi ⟨by omega, hai⟩
  have claim : ∀ i ≤ Nat.find hcon, ∀ x, S.dom x →
      (∃ i' ≤ i, x = a i') ∨ S.rel 0 [a i, x] := by
    intro i
    induction i with
    | zero =>
      intro _ x hx
      rcases F_least P S hS ho (hda 0 (by omega)) hx with h | h
      · exact Or.inl ⟨0, le_refl _, h⟩
      · exact Or.inr h
    | succ i ih =>
      intro hi x hx
      rcases ih (by omega) x hx with ⟨i', hi', rfl⟩ | h
      · exact Or.inl ⟨i', by omega, rfl⟩
      · have hai : S.dom (a i) := hda i (by omega)
        have hai1 : S.dom (a (i + 1)) := hda (i + 1) (by omega)
        rcases F_lin P S hS hx hai1 with h' | h' | h'
        · exact (F_imm P S hS he hde hai hai1 hx (ha i (by omega)) (hmin i (by omega)) h h').elim
        · exact Or.inl ⟨i + 1, le_refl _, h'⟩
        · exact Or.inr h'
  have hall : ∀ x, S.dom x → ∃ i ≤ Nat.find hcon, x = a i := by
    intro x hx
    rcases claim _ (le_refl _) x hx with h | h
    · exact h
    · rw [hj0.2] at h
      exfalso
      rcases F_greatest P S hS he hde hx with h' | h'
      · subst h'; exact F_irrefl P S hS hde h
      · exact F_irrefl P S hS hde (F_trans P S hS hde hde hx h h')
  choose g hg hga using fun k : Fin (T + 1) => hall (d k) (hdd k)
  have hinj : Function.Injective
      (fun k : Fin (T + 1) => (⟨g k, by have := hg k; omega⟩ : Fin (Nat.find hcon + 1))) := by
    intro k k' h
    apply hd
    simp only [Fin.mk.injEq] at h
    rw [hga k, hga k', h]
  have := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin] at this
  omega

include hS ho he ha hda hde hd hdd in
/-- The chain is strictly increasing up to time `T`. -/
theorem chain_lt : ∀ k i, i + k + 1 ≤ T → S.rel 0 [a i, a (i + k + 1)] := by
  intro k
  induction k with
  | zero =>
    intro i hi
    exact F_succ P S hS he hde (hda i (by omega)) (hda (i + 1) (by omega)) (ha i (by omega))
      (no_early_e P S hS a e ho he ha hda hde d hd hdd i (by omega))
  | succ k ih =>
    intro i hi
    have h1 := ih i (by omega)
    have h2 := ih (i + 1) (by omega)
    rw [show i + 1 + k + 1 = i + (k + 1) + 1 by omega] at h2
    have h3 : S.rel 0 [a (i + k + 1), a (i + (k + 1) + 1)] := by
      have := F_succ P S hS he hde (hda (i + k + 1) (by omega)) (hda (i + k + 2) (by omega))
        (ha (i + k + 1) (by omega))
        (no_early_e P S hS a e ho he ha hda hde d hd hdd (i + k + 1) (by omega))
      rwa [show i + (k + 1) + 1 = i + k + 1 + 1 by omega]
    exact F_trans P S hS (hda i (by omega)) (hda _ (by omega)) (hda _ (by omega)) h1 h3

include hS ho he ha hda hde hd hdd in
/-- The predecessor of `a_k` is identified by the order: if `x < a_k` and `S(x) = a_k` then
`x = a_{k-1}`. -/
theorem ident {x : U} (hx : S.dom x) {k : ℕ} (hk1 : 1 ≤ k) (hkT : k ≤ T)
    (hlt : S.rel 0 [x, a k]) (hsx : S.fn 2 [x] = some (a k)) : x = a (k - 1) := by
  have hak := hda k hkT
  have hak1 := hda (k - 1) (by omega)
  have hxe : x ≠ e := by
    intro h
    subst h
    rcases F_greatest P S hS he hde hak with h' | h'
    · rw [h'] at hlt; exact F_irrefl P S hS hde hlt
    · exact F_irrefl P S hS hde (F_trans P S hS hde hde hak hlt h')
  have hch : S.rel 0 [a (k - 1), a k] := by
    have := chain_lt P S hS a e ho he ha hda hde d hd hdd 0 (k - 1) (by omega)
    rwa [show k - 1 + 0 + 1 = k by omega] at this
  have hne1 : a (k - 1) ≠ e := no_early_e P S hS a e ho he ha hda hde d hd hdd (k - 1) (by omega)
  have hs1 : S.fn 2 [a (k - 1)] = some (a k) := by
    have := ha (k - 1) (by omega)
    rwa [show k - 1 + 1 = k by omega] at this
  rcases F_lin P S hS hx hak1 with h | h | h
  · exact (F_imm P S hS he hde hx hak hak1 hsx hxe h hch).elim
  · exact h
  · exact (F_imm P S hS he hde hak1 hak hx hs1 hne1 h hlt).elim

include hS hT' ho he ha hc hs hda hde hdc hds hd hdd in
/-- Step 2: the partial structure follows the true run up to time `T`. -/
theorem sim : ∀ j ≤ T, S.rel (1 + P.norm (P.cfg j).1) [a j] ∧
    ∀ r < P.ncnt, cv r j = a ((P.cfg j).2 r)
  | 0, _ => by
    refine ⟨?_, fun r hr => ?_⟩
    · have : P.norm (P.cfg 0).1 = 0 := by simp [Prog.cfg_zero, Prog.norm]
      rw [this]; exact F_q0 P S hS ho (hda 0 (by omega))
    · rw [F_c0 P S hS hr ho (hda 0 (by omega)) (hdc 0 (by omega) r hr) (hc 0 (by omega) r hr)]
      rfl
  | j + 1, hj => by
    obtain ⟨hQ, hC⟩ := sim j (by omega)
    have hjT : j < T := by omega
    have hne := no_early_e P S hS a e ho he ha hda hde d hd hdd j hjT
    set ℓ := (P.cfg j).1 with hℓdef
    have hnh := hT' j hjT
    have hℓ : ℓ < P.length := by
      by_contra h; exact hnh (Or.inl (by omega))
    have hnorm : P.norm ℓ = ℓ := by unfold Prog.norm; omega
    rw [hnorm] at hQ
    obtain ⟨i, hi⟩ : ∃ i, P[ℓ]? = some i := ⟨_, List.getElem?_eq_getElem hℓ⟩
    have haj := hda j (by omega)
    have haj1 := hda (j + 1) hj
    have hv := ha j hjT
    rcases i with ⟨r, ℓ'⟩ | ⟨r, ℓ₀, ℓ₁⟩ | u
    · -- increment
      obtain ⟨hs1, hs2, hs3⟩ := next_inc P hℓdef.symm hi
      have hr : r < P.ncnt := P.instrCnt_lt hi
      refine ⟨?_, fun r' hr' => ?_⟩
      · rw [hs1]; exact T_inc_st P S hS hℓ he hne hQ hv hde haj haj1 hi
      · by_cases hrr : r' = r
        · subst hrr
          have hk : (P.cfg j).2 r' ≤ j := P.cfg_le j r'
          have hcj : S.fn (3 + r') [a j] = some (a ((P.cfg j).2 r')) := by
            rw [← hC r' hr]; exact hc j (by omega) r' hr
          have h := T_inc_cnt P S hS hℓ he hne hQ hv hde haj haj1 hi
            (hda _ (by omega)) (hda ((P.cfg j).2 r' + 1) (by omega)) hcj (ha _ (by omega))
            ⟨_, hc (j + 1) hj r' hr⟩
          rw [hc (j + 1) hj r' hr] at h
          rw [hs2]; exact Option.some.inj h
        · have h := T_inc_same P S hS hℓ he hne hQ hv hde haj haj1 hi hr' hrr
            (hdc j (by omega) r' hr') (hc j (by omega) r' hr') ⟨_, hc (j + 1) hj r' hr'⟩
          rw [hc (j + 1) hj r' hr'] at h
          rw [Option.some.inj h, hC r' hr', hs3 r' hrr]
    · -- decrement
      have hr : r < P.ncnt := P.instrCnt_lt hi
      have hk : (P.cfg j).2 r ≤ j := P.cfg_le j r
      have hcj : S.fn (3 + r) [a j] = some (a ((P.cfg j).2 r)) := by
        rw [← hC r hr]; exact hc j (by omega) r hr
      have hod := hda 0 (by omega)
      by_cases hz : (P.cfg j).2 r = 0
      · obtain ⟨hs1, hs2⟩ := next_dec_zero P hℓdef.symm hi hz
        have hco : S.fn (3 + r) [a j] = some (a 0) := by rw [hcj, hz]
        refine ⟨?_, fun r' hr' => ?_⟩
        · rw [hs1]; exact T_dz_st P S hS hℓ he hne hQ hv hde haj haj1 ho hod hi hco
        · rw [hs2 r']
          by_cases hrr : r' = r
          · subst hrr
            have h := T_dz_cnt P S hS hℓ he hne hQ hv hde haj haj1 ho hod hi hco
              ⟨_, hc (j + 1) hj r' hr⟩
            rw [hc (j + 1) hj r' hr] at h
            rw [Option.some.inj h, hz]
          · have h := T_dz_same P S hS hℓ he hne hQ hv hde haj haj1 ho hod hi hco hr' hrr
              (hdc j (by omega) r' hr') (hc j (by omega) r' hr') ⟨_, hc (j + 1) hj r' hr'⟩
            rw [hc (j + 1) hj r' hr'] at h
            rw [Option.some.inj h, hC r' hr']
      · obtain ⟨hs1, hs2, hs3⟩ := next_dec_pos P hℓdef.symm hi hz
        have hak := hda ((P.cfg j).2 r) (by omega)
        have hco : a ((P.cfg j).2 r) ≠ a 0 := by
          intro h
          have := chain_lt P S hS a e ho he ha hda hde d hd hdd ((P.cfg j).2 r - 1) 0 (by omega)
          rw [show 0 + ((P.cfg j).2 r - 1) + 1 = (P.cfg j).2 r by omega, h] at this
          exact F_irrefl P S hS hod this
        refine ⟨?_, fun r' hr' => ?_⟩
        · rw [hs1]; exact T_dp_st P S hS hℓ he hne hQ hv hde haj haj1 ho hod hi hak hcj hco
        · by_cases hrr : r' = r
          · subst hrr
            have hdd' := hdc (j + 1) hj r' hr
            have hlt := T_dp_lt P S hS hℓ he hne hQ hv hde haj haj1 ho hod hi hak hdd' hcj hco
              (hc (j + 1) hj r' hr)
            have hsv := T_dp_s P S hS hℓ he hne hQ hv hde haj haj1 ho hod hi hak hdd'
              (hds (j + 1) hj r' hr) hcj hco (hc (j + 1) hj r' hr) (hs (j + 1) hj r' hr)
            have hS2 : S.fn 2 [cv r' (j + 1)] = some (a ((P.cfg j).2 r')) := by
              rw [← hsv]; exact hs (j + 1) hj r' hr
            rw [hs2]
            exact ident P S hS a e ho he ha hda hde d hd hdd hdd' (by omega) (by omega) hlt hS2
          · rw [hs3 r' hrr]
            have h := T_dp_same P S hS hℓ he hne hQ hv hde haj haj1 ho hod hi hak hcj hco hr' hrr
              (hdc j (by omega) r' hr') (hc j (by omega) r' hr') ⟨_, hc (j + 1) hj r' hr'⟩
            rw [hc (j + 1) hj r' hr'] at h
            rw [Option.some.inj h, hC r' hr']
    · -- a halt instruction cannot be active before time `T`
      exact absurd (Or.inr (by rw [hi])) hnh

include hS hT' ho he ha hc hs hda hde hdc hds hd hdd in
/-- **The local switch.**  If the run first halts at time `T`, no partial structure containing
the named terms and `T + 1` distinct elements satisfies all defined instances of `θ_M`. -/
theorem theta_local (hT : P.IsHaltSt (P.cfg T).1) : False := by
  obtain ⟨hQ, -⟩ := sim P S hS hT' a e cv sv ho he ha hc hs hda hde hdc hds d hd hdd T (le_refl _)
  exact F_halt P S hS (P.norm_le _) (P.halt_norm hT) (hda T (le_refl _)) hQ

end Local

/-! ### Direction (ii) for arbitrary structures -/

/-- The first halting time. -/
theorem Prog.first_halt (P : Prog) (hP : P.Halts) :
    ∃ T, P.IsHaltSt (P.cfg T).1 ∧ ∀ j < T, ¬ P.IsHaltSt (P.cfg j).1 := by
  classical
  exact ⟨Nat.find hP, Nat.find_spec hP, fun j hj => Nat.find_min hP hj⟩

/-- **The switch, direction (ii)** (manuscript `lem:switch` (ii)): if the run first halts at
time `T`, then `θ_M` has no model on any type with `T + 1` distinct elements, finite or
infinite.  Only finitely many clause instances are used; no well-ordering is assumed. -/
theorem no_large_model (P : Prog) {T : ℕ} (hT : P.IsHaltSt (P.cfg T).1)
    (hT' : ∀ j < T, ¬ P.IsHaltSt (P.cfg j).1) {U : Type} (M : Str U)
    (hM : IsModel (theta P) M) (d : Fin (T + 1) → U) (hd : Function.Injective d) : False := by
  let a : ℕ → U := fun j => (fun x => M.fn 2 [x])^[j] (M.fn 0 [])
  have ha : ∀ j, M.fn 2 [a j] = a (j + 1) := fun j => by
    simp only [a]; rw [Function.iterate_succ_apply']
  exact theta_local P M.toP (locSat_of_model _ M hM) hT' a (M.fn 1 [])
    (fun r j => M.fn (3 + r) [a j]) (fun r j => M.fn 2 [M.fn (3 + r) [a j]]) rfl rfl
    (fun j _ => by simp only [Str.toP]; rw [ha j]) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun _ _ => trivial) trivial (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial) d hd
    (fun _ => trivial) hT

theorem no_model_of_size (P : Prog) {T : ℕ} (hT : P.IsHaltSt (P.cfg T).1)
    (hT' : ∀ j < T, ¬ P.IsHaltSt (P.cfg j).1) {n : ℕ} (hn : T + 1 ≤ n) :
    ¬ HasModelOfSize (theta P) n := by
  rintro ⟨M, hM⟩
  exact no_large_model P hT hT' M hM (fun i => ⟨i.val, by omega⟩)
    (fun i j h => Fin.ext (by simpa using congrArg Fin.val h))

/-! ### The term DAG of the halting trace -/

section DAGDef
variable (P : Prog) (T : ℕ)

/-- Node index of `a_j = S^j(o)`. -/
def aIdx (j : ℕ) : ℕ := if j = 0 then 0 else j + 1

/-- Node index of `C_r(a_j)`; the next index is `S(C_r(a_j))`. -/
def cIdx (r j : ℕ) : ℕ := T + 2 + 2 * (j * P.ncnt + r)

/-- The DAG: `o, e, a_1, …, a_T`, then `C_r(a_j), S(C_r(a_j))` for `j ≤ T`, `r < K`. -/
def thDAG : DAG where
  sym k := if k = 0 then 0 else if k = 1 then 1 else if k < T + 2 then 2 else
    if (k - (T + 2)) % 2 = 0 then 3 + (k - (T + 2)) / 2 % P.ncnt else 2
  args k := if k < 2 then [] else if k < T + 2 then [aIdx (k - 2)] else
    if (k - (T + 2)) % 2 = 0 then [aIdx ((k - (T + 2)) / 2 / P.ncnt)] else [k - 1]

/-- The number of nodes. -/
def thM : ℕ := T + 2 + 2 * P.ncnt * (T + 1)

theorem ncnt_pos : 0 < P.ncnt := by unfold Prog.ncnt; omega

theorem aIdx_le (j : ℕ) : aIdx j ≤ j + 1 := by unfold aIdx; split_ifs <;> omega

theorem thDAG_valid : (thDAG P T).Valid (theta P) (thM P T) := by
  intro k hk
  have hK := ncnt_pos P
  simp only [thDAG, theta, Sentence.funs, thFuns_length]
  by_cases h0 : k = 0
  · subst h0; exact ⟨by simp, rfl, by simp⟩
  by_cases h1 : k = 1
  · subst h1; exact ⟨by simp, rfl, by simp⟩
  by_cases h2 : k < T + 2
  · have hk2 : ¬ k < 2 := by omega
    simp only [h0, h1, h2, hk2, if_false, if_true, List.length_singleton, List.mem_singleton,
      forall_eq, thFuns_getD_S]
    refine ⟨by omega, trivial, ?_⟩
    have := aIdx_le (k - 2); unfold aIdx; split_ifs <;> omega
  · have hk2 : ¬ k < 2 := by omega
    simp only [h0, h1, h2, hk2, if_false]
    split_ifs with he
    · have hr : (k - (T + 2)) / 2 % P.ncnt < P.ncnt := Nat.mod_lt _ hK
      simp only [List.length_singleton, List.mem_singleton, forall_eq, thFuns_getD_C P hr]
      refine ⟨by omega, trivial, ?_⟩
      have hq : (k - (T + 2)) / 2 < P.ncnt * (T + 1) := by
        unfold thM at hk
        have : k - (T + 2) < 2 * (P.ncnt * (T + 1)) := by rw [← mul_assoc]; omega
        omega
      have hq' : (k - (T + 2)) / 2 / P.ncnt < T + 1 := Nat.div_lt_of_lt_mul hq
      have := aIdx_le ((k - (T + 2)) / 2 / P.ncnt)
      omega
    · simp only [List.length_singleton, List.mem_singleton, forall_eq, thFuns_getD_S]
      exact ⟨by omega, trivial, by omega⟩

theorem sym_zero : (thDAG P T).sym 0 = 0 := rfl
theorem args_zero : (thDAG P T).args 0 = [] := rfl
theorem sym_one : (thDAG P T).sym 1 = 1 := rfl
theorem args_one : (thDAG P T).args 1 = [] := rfl

theorem sym_a {j : ℕ} (hj : j < T) : (thDAG P T).sym (aIdx (j + 1)) = 2 ∧
    (thDAG P T).args (aIdx (j + 1)) = [aIdx j] := by
  have e : aIdx (j + 1) = j + 2 := by simp [aIdx]
  rw [e]
  simp only [thDAG]
  refine ⟨?_, ?_⟩
  · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  · rw [if_neg (by omega), if_pos (by omega)]
    simp

theorem sym_c {r : ℕ} (hr : r < P.ncnt) (j : ℕ) : (thDAG P T).sym (cIdx P T r j) = 3 + r ∧
    (thDAG P T).args (cIdx P T r j) = [aIdx j] := by
  have hK := ncnt_pos P
  have e1 : cIdx P T r j - (T + 2) = 2 * (j * P.ncnt + r) := by unfold cIdx; omega
  have e2 : 2 * (j * P.ncnt + r) % 2 = 0 := by omega
  have e3 : 2 * (j * P.ncnt + r) / 2 = j * P.ncnt + r := by omega
  have e4 : (j * P.ncnt + r) % P.ncnt = r := by
    rw [Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hr
  have e5 : (j * P.ncnt + r) / P.ncnt = j := by
    rw [Nat.mul_comm, Nat.mul_add_div hK, Nat.div_eq_of_lt hr]; omega
  simp only [thDAG]
  have hc2 : ¬ cIdx P T r j < T + 2 := by unfold cIdx; omega
  refine ⟨?_, ?_⟩
  · rw [if_neg (by unfold cIdx; omega), if_neg (by unfold cIdx; omega), if_neg hc2, e1,
      if_pos e2, e3, e4]
  · rw [if_neg (by unfold cIdx; omega), if_neg hc2, e1, if_pos e2, e3, e5]

theorem sym_s {r : ℕ} (_hr : r < P.ncnt) (j : ℕ) : (thDAG P T).sym (cIdx P T r j + 1) = 2 ∧
    (thDAG P T).args (cIdx P T r j + 1) = [cIdx P T r j] := by
  have e1 : cIdx P T r j + 1 - (T + 2) = 2 * (j * P.ncnt + r) + 1 := by unfold cIdx; omega
  have e2 : ¬ (2 * (j * P.ncnt + r) + 1) % 2 = 0 := by omega
  simp only [thDAG]
  have hc2 : ¬ cIdx P T r j + 1 < T + 2 := by unfold cIdx; omega
  refine ⟨?_, ?_⟩
  · rw [if_neg (by unfold cIdx; omega), if_neg (by unfold cIdx; omega), if_neg hc2, e1,
      if_neg e2]
  · rw [if_neg (by unfold cIdx; omega), if_neg hc2, e1, if_neg e2]
    simp

theorem cIdx_lt {r : ℕ} (hr : r < P.ncnt) {j : ℕ} (hj : j ≤ T) :
    cIdx P T r j + 1 < thM P T := by
  unfold cIdx thM
  have : j * P.ncnt + r < P.ncnt * (T + 1) := by
    calc j * P.ncnt + r < j * P.ncnt + P.ncnt := by omega
      _ = (j + 1) * P.ncnt := by ring
      _ ≤ (T + 1) * P.ncnt := Nat.mul_le_mul_right _ (by omega)
      _ = P.ncnt * (T + 1) := by ring
  have : 2 * (j * P.ncnt + r) + 1 < 2 * (P.ncnt * (T + 1)) := by omega
  rw [mul_assoc]; omega

theorem aIdx_lt {j : ℕ} (hj : j ≤ T) : aIdx j < thM P T := by
  have := aIdx_le j; unfold thM; omega

end DAGDef

/-! ### The eventual degree bound -/

section Bound
variable (P : Prog) (K : Type) [Field K]

/-- The halting-case degree bound `C_M` (depends on `M` and its halting time only). -/
def haltBound (T : ℕ) : ℕ :=
  thM P T + atomBound (theta P) (thM P T + (T + 1)) + maxWidth (theta P)

theorem theta_nsRefutes {T : ℕ} (hT : P.IsHaltSt (P.cfg T).1)
    (hT' : ∀ j < T, ¬ P.IsHaltSt (P.cfg j).1) {n : ℕ} (hn : T + 1 ≤ n) :
    NSRefutes ((template (theta P) K).inst n) (haltBound P T) := by
  classical
  have hn0 : 0 < n := by omega
  let lab : Fin (T + 1) → Fin n := fun i => ⟨i.val, by omega⟩
  have hlab : Function.Injective lab := fun i j h => Fin.ext (by simpa [lab] using h)
  let D : Finset (Fin n) := Finset.univ.image lab
  have hD : D.card = T + 1 := by
    rw [Finset.card_image_of_injective _ hlab, Finset.card_univ, Fintype.card_fin]
  have h := nsRefutes_of_local (theta P) K hn0 (thDAG P T) (theta_WF P) (thDAG_valid P T) D ?_
  · rw [hD] at h; exact h
  intro α hα β hloc
  set S := pstrOf (theta P) hn0 (thDAG P T) α D β
  -- node values
  have hnode : ∀ k (hk : k < thM P T), S.fn ((thDAG P T).sym k)
      (((thDAG P T).args k).map (av hn0 α)) = some (av hn0 α k) := by
    intro k hk
    have := pstrOf_fn_node (theta P) hn0 (thDAG P T) α hα D β ⟨k, hk⟩
    simpa only [nodeIn, av, dif_pos hk] using this
  have hdomv : ∀ k < thM P T, S.dom (av hn0 α k) := by
    intro k hk
    show av hn0 α k ∈ Eset α D
    simp only [av, dif_pos hk]
    exact mem_Eset α D _
  have hM0 : 0 < thM P T := by unfold thM; omega
  refine theta_local P S hloc hT' (fun j => av hn0 α (aIdx j)) (av hn0 α 1)
    (fun r j => av hn0 α (cIdx P T r j)) (fun r j => av hn0 α (cIdx P T r j + 1)) ?_ ?_ ?_ ?_ ?_
    (fun j hj => hdomv _ (aIdx_lt P T hj)) (hdomv 1 (by unfold thM; omega))
    (fun j hj r hr => hdomv _ (by have := cIdx_lt P T hr hj; omega))
    (fun j hj r hr => hdomv _ (cIdx_lt P T hr hj)) (fun i => lab i) hlab ?_ hT
  · have := hnode 0 hM0
    rw [sym_zero, args_zero] at this
    simpa [aIdx] using this
  · have := hnode 1 (by unfold thM; omega)
    rw [sym_one, args_one] at this
    simpa using this
  · intro j hj
    have := hnode (aIdx (j + 1)) (aIdx_lt P T (by omega))
    rw [(sym_a P T hj).1, (sym_a P T hj).2] at this
    simpa using this
  · intro j hj r hr
    have := hnode (cIdx P T r j) (by have := cIdx_lt P T hr hj; omega)
    rw [(sym_c P T hr j).1, (sym_c P T hr j).2] at this
    simpa using this
  · intro j hj r hr
    have := hnode (cIdx P T r j + 1) (cIdx_lt P T hr hj)
    rw [(sym_s P T hr j).1, (sym_s P T hr j).2] at this
    simpa using this
  · intro i
    show lab i ∈ Eset α D
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem lab (Finset.mem_univ i))

/-- **Eventual bounded degree in the halting case** (manuscript `lem:switch` (iii)): if `M`
halts, there are `C_M` and `N_M` with NS degree at most `C_M` at every size `n ≥ N_M`. -/
theorem theta_eventually_bounded (hP : P.Halts) :
    ∃ C N : ℕ, ∀ n, N ≤ n → nsDegree ((template (theta P) K).inst n) ≤ (C : ℕ∞) := by
  obtain ⟨T, hT, hT'⟩ := P.first_halt hP
  exact ⟨haltBound P T, T + 1, fun n hn =>
    (nsDegree_le_iff _ _).mpr (theta_nsRefutes P K hT hT' hn)⟩

end Bound

end ClaudeUndec
