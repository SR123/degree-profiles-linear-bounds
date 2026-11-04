/-
Claude, 27 Sep 2026.  Undecidability, part D3: halting of counter machines from the zero
configuration is as hard as Mathlib's halting problem.

Imported theorem (Mathlib, `Mathlib/Computability/Halting.lean`):

    ComputablePred.halting_problem (n : ℕ) : ¬ ComputablePred fun c => (Nat.Partrec.Code.eval c n).Dom

Adapter.  By `Nat.Partrec.Code.evaln_complete`, `(eval c 0).Dom ↔ ∃ k, (evaln k c 0).isSome`, and
`H(k, m) := if (evaln k (ofNat Code m) 0).isSome then 0 else 1` is primitive recursive
(`Nat.Partrec.Code.primrec_evaln`), hence `Nat.Primrec'`.  `UCompile` turns `H` into counter code
`hCode`.  The machine `univProg m` loads `m` into register `0` and then runs the search

    k := 0;  loop { T := H(k, m); if T = 0 then halt; k := k + 1 }.

`univProg_halts_iff`: `(univProg m).Halts ↔ ∃ k, H(k, m) = 0`, both directions proved from the
step semantics.  `univProg` is primitive recursive in `m` (a fixed list followed by `m`
increments).  Hence `(eval c 0).Dom ↔ (univProg (encode c)).Halts`.
-/
import UCompile
import Mathlib.Computability.Halting

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ClaudeUndec
open Function Nat.Partrec

/-! ### The search predicate -/

/-- `H(k, m) = 0` iff code number `m` halts on input `0` within `k` steps (`evaln`). -/
def hfun (k m : ℕ) : ℕ :=
  bif (Code.evaln k (Denumerable.ofNat Code m) 0).isSome then 0 else 1

theorem hfun_primrec : Primrec₂ hfun := by
  have h1 : Primrec fun p : ℕ × ℕ => Code.evaln p.1 (Denumerable.ofNat Code p.2) 0 :=
    Code.primrec_evaln.comp ((Primrec.fst.pair ((Primrec.ofNat Code).comp Primrec.snd)).pair
      (Primrec.const 0))
  exact Primrec.cond (Primrec.option_isSome.comp h1) (Primrec.const 0) (Primrec.const 1)

theorem hfun_primrec' : @Nat.Primrec' 2 fun v => hfun v.head v.tail.head :=
  Nat.Primrec'.prim_iff₂.mpr hfun_primrec

theorem eval_dom_iff (c : Code) : (Code.eval c 0).Dom ↔ ∃ k, hfun k (Encodable.encode c) = 0 := by
  simp only [hfun, Denumerable.ofNat_encode]
  rw [Part.dom_iff_mem]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨k, hk⟩ := Code.evaln_complete.mp hx
    refine ⟨k, ?_⟩
    rw [Option.mem_def] at hk
    simp [hk]
  · rintro ⟨k, hk⟩
    cases h : Code.evaln k c 0 with
    | none => simp [h] at hk
    | some x => exact ⟨x, Code.evaln_complete.mpr ⟨k, h⟩⟩

/-! ### The universal machine -/

/-- Argument registers of the search: `H(k, m)` with `k` in register `1`, `m` in register `0`. -/
def hIns : Fin 2 → ℕ := ![1, 0]

theorem hCode_exists : ∃ code len, Computes (fun v => hfun v.head v.tail.head) hIns 2 4 code len :=
  primrec_compiles hfun_primrec' hIns 2 4 (fun i => by fin_cases i <;> simp [hIns]) (by omega)

/-- Counter code for `T := H(k, m)` (register `2`), scratch from register `4`; register `3` is
never touched and serves as a zero register for unconditional jumps. -/
noncomputable def hCode : ℕ → List Instr := Classical.choose hCode_exists
noncomputable def hLen : ℕ := Classical.choose (Classical.choose_spec hCode_exists)
theorem hCode_spec : Computes (fun v => hfun v.head v.tail.head) hIns 2 4 hCode hLen :=
  Classical.choose_spec (Classical.choose_spec hCode_exists)

/-- The fixed search part, placed at address `1`. -/
noncomputable def searchPart : List Instr :=
  hCode 1 ++ [decI 2 (hLen + 3) (hLen + 2), incI 1 1, haltI]

/-- The load part: `m` increments of register `0`, then a jump to address `1`. -/
def loadPart (L m : ℕ) : List Instr :=
  (List.range m).map (fun i => incI 0 (L + i + 1)) ++ [decI 3 1 1]

/-- The fixed prefix: a jump to the load part, then the search part. -/
noncomputable def univPre : List Instr := [decI 3 (hLen + 4) (hLen + 4)] ++ searchPart

/-- **The universal machine for input code number `m`.** -/
noncomputable def univProg (m : ℕ) : Prog := univPre ++ loadPart (hLen + 4) m

section Run
variable (m : ℕ)

theorem hCode_len : (hCode 1).length = hLen := hCode_spec.1 1

theorem univPre_length : univPre.length = hLen + 4 := by
  simp [univPre, searchPart, hCode_len]

theorem univ_get_start : (univProg m)[0]? = some (decI 3 (hLen + 4) (hLen + 4)) := by
  simp [univProg, univPre]

theorem univ_get_pre {i : ℕ} (hi : i < hLen + 4) : (univProg m)[i]? = univPre[i]? := by
  unfold univProg
  rw [List.getElem?_append_left (by rw [univPre_length]; exact hi)]

theorem univ_emb_h : Emb (univProg m) 1 (hCode 1) := by
  intro i hi
  rw [hCode_len] at hi
  rw [univ_get_pre m (by omega)]
  simp only [univPre, searchPart, List.append_assoc]
  rw [show 1 + i = [decI 3 (hLen + 4) (hLen + 4)].length + i by simp [Nat.add_comm],
    List.getElem?_append_right (by simp), List.getElem?_append_left (by simp [hCode_len]; omega)]
  simp [hCode_len, List.getElem?_eq_getElem (hCode_len ▸ hi)]

theorem univ_get_search {i : ℕ} (hi : i < 3) : (univProg m)[hLen + 1 + i]? =
    [decI 2 (hLen + 3) (hLen + 2), incI 1 1, haltI][i]? := by
  rw [univ_get_pre m (by omega)]
  simp only [univPre, searchPart, List.append_assoc]
  rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp [hCode_len])]
  congr 1
  simp [hCode_len]

theorem univ_get_test : (univProg m)[hLen + 1]? = some (decI 2 (hLen + 3) (hLen + 2)) := by
  simpa using univ_get_search m (i := 0) (by omega)

theorem univ_get_inc : (univProg m)[hLen + 2]? = some (incI 1 1) := by
  simpa using univ_get_search m (i := 1) (by omega)

theorem univ_get_halt : (univProg m)[hLen + 3]? = some haltI := by
  simpa using univ_get_search m (i := 2) (by omega)

theorem univ_get_loadPart (i : ℕ) : (univProg m)[hLen + 4 + i]? = (loadPart (hLen + 4) m)[i]? := by
  unfold univProg
  rw [List.getElem?_append_right (by rw [univPre_length]; omega), univPre_length]
  congr 1; omega

theorem univ_get_load {i : ℕ} (hi : i < m) :
    (univProg m)[hLen + 4 + i]? = some (incI 0 (hLen + 4 + i + 1)) := by
  rw [univ_get_loadPart]
  simp only [loadPart]
  rw [List.getElem?_append_left (by simp; omega)]
  simp [hi]

theorem univ_get_jump : (univProg m)[hLen + 4 + m]? = some (decI 3 1 1) := by
  rw [univ_get_loadPart]
  simp only [loadPart]
  rw [List.getElem?_append_right (by simp)]
  simp

/-- Loading: after the initial jump and `m` increments the search starts at address `1`. -/
theorem univ_load : ∃ t, ReachN (univProg m) (0, fun _ => 0) (1, update (fun _ => 0) 0 m) t := by
  have r0 := ReachN.step (c := ((0 : ℕ), fun _ : ℕ => (0 : ℕ))) (univ_get_start m) (decI_ne _ _ _)
  rw [step_at_dec_zero (univ_get_start m) rfl] at r0
  have hl : ∀ i ≤ m, ∃ t, ReachN (univProg m) (hLen + 4, fun _ => 0)
      (hLen + 4 + i, update (fun _ => 0) 0 i) t := by
    intro i
    induction i with
    | zero => intro _; exact ⟨0, by simpa using ReachN.refl (P := univProg m) _⟩
    | succ i ih =>
      intro hi
      obtain ⟨t, ht⟩ := ih (by omega)
      have r := ReachN.step (c := (hLen + 4 + i, update (fun _ : ℕ => (0 : ℕ)) 0 i))
        (univ_get_load m (by omega)) (incI_ne _ _)
      rw [step_at_inc (univ_get_load m (by omega))] at r
      refine ⟨_, ht.trans (by simpa [update_idem, add_assoc] using r)⟩
  obtain ⟨t, ht⟩ := hl m le_rfl
  have rj := ReachN.step (c := (hLen + 4 + m, update (fun _ : ℕ => (0 : ℕ)) 0 m))
    (univ_get_jump m) (decI_ne _ _ _)
  rw [step_at_dec_zero (univ_get_jump m) (by simp)] at rj
  exact ⟨_, (r0.trans ht).trans rj⟩

/-- One round of the search, when `H(k, m) ≠ 0`. -/
theorem univ_round {ρ : ℕ → ℕ} (h0 : ρ 0 = m) (h3 : ρ 3 = 0)
    (hk : hfun (ρ 1) m ≠ 0) : ∃ ρ' t, ReachN (univProg m) (1, ρ) (1, ρ') t ∧ 1 ≤ t ∧
      ρ' 0 = m ∧ ρ' 1 = ρ 1 + 1 ∧ ρ' 3 = 0 := by
  obtain ⟨ρ₁, ⟨t₁, r₁⟩, hT, hkeep⟩ := hCode_spec.2 (univProg m) 1 ρ (univ_emb_h m)
  replace hT : ρ₁ 2 = hfun (ρ 1) m := by
    rw [hT, ← h0]; simp only; simp [hIns, List.Vector.tail_ofFn]
  have ht := univ_get_test m
  rw [show hLen + 1 = 1 + hLen by omega] at ht
  have r₂ := ReachN.step (c := (1 + hLen, ρ₁)) ht (decI_ne _ _ _)
  rw [step_at_dec_pos ht (by rw [hT]; exact hk)] at r₂
  have r₃ := ReachN.step (c := (hLen + 2, update ρ₁ 2 (ρ₁ 2 - 1))) (univ_get_inc m) (incI_ne _ _)
  rw [step_at_inc (univ_get_inc m)] at r₃
  refine ⟨_, _, (r₁.trans r₂).trans r₃, by omega, ?_, ?_, ?_⟩
  · simp [update_apply, hkeep 0 (by omega) (by omega), h0]
  · simp [update_apply, hkeep 1 (by omega) (by omega)]
  · simp [update_apply, hkeep 3 (by omega) (by omega), h3]

/-- Reaching round `k` when the first `k` rounds do not stop. -/
theorem univ_rounds : ∀ k, (∀ k' < k, hfun k' m ≠ 0) →
    ∃ ρ t, ReachN (univProg m) (0, fun _ => 0) (1, ρ) t ∧ k ≤ t ∧ ρ 0 = m ∧ ρ 1 = k ∧ ρ 3 = 0
  | 0, _ => by
    obtain ⟨t, ht⟩ := univ_load m
    exact ⟨_, t, ht, by omega, by simp, by simp, by simp⟩
  | k + 1, hk => by
    obtain ⟨ρ, t, ht, hkt, h0, h1, h3⟩ := univ_rounds k (fun k' hk' => hk k' (by omega))
    obtain ⟨ρ', t', ht', ht1, h0', h1', h3'⟩ := univ_round m h0 h3 (by rw [h1]; exact hk k (by omega))
    exact ⟨ρ', _, ht.trans ht', by omega, h0', by rw [h1', h1], h3'⟩

/-- **The universal machine halts iff the search succeeds.** -/
theorem univProg_halts_iff : (univProg m).Halts ↔ ∃ k, hfun k m = 0 := by
  classical
  constructor
  · rintro ⟨j, hj⟩
    by_contra hno
    push_neg at hno
    obtain ⟨ρ, t, ht, hkt, -⟩ := univ_rounds m (j + 1) (fun k' _ => hno k')
    exact ht.2 j (by omega) hj
  · intro hex
    obtain ⟨ρ, t, ht, -, h0, h1, h3⟩ := univ_rounds m (Nat.find hex)
      (fun k' hk' => Nat.find_min hex hk')
    obtain ⟨ρ₁, ⟨t₁, r₁⟩, hT, -⟩ := hCode_spec.2 (univProg m) 1 ρ (univ_emb_h m)
    replace hT : ρ₁ 2 = 0 := by
      have e : ρ₁ 2 = hfun (ρ 1) (ρ 0) := by rw [hT]; simp only; simp [hIns, List.Vector.tail_ofFn]
      rw [e, h1, h0]; exact Nat.find_spec hex
    have htest := univ_get_test m
    rw [show hLen + 1 = 1 + hLen by omega] at htest
    have r₂ := ReachN.step (c := (1 + hLen, ρ₁)) htest (decI_ne _ _ _)
    rw [step_at_dec_zero htest hT] at r₂
    have hall := (ht.trans r₁).trans r₂
    refine ⟨t + t₁ + 1, ?_⟩
    unfold Prog.cfg
    rw [hall.1]
    exact Or.inr (univ_get_halt m)

end Run

/-- **Reduction of Mathlib's halting problem to counter-machine halting.** -/
theorem eval_dom_iff_halts (c : Code) :
    (Code.eval c 0).Dom ↔ (univProg (Encodable.encode c)).Halts := by
  rw [eval_dom_iff, univProg_halts_iff]

end ClaudeUndec
