/-
Claude, 27 Sep 2026.  Undecidability, part D2: every primitive recursive function is computed by
counter-machine code (Mathlib's `Nat.Primrec'`, the vector form of primitive recursion).

`Block code len R`: the relocatable code `code a` (of length `len`) placed at address `a`, run
from any register contents `ρ`, reaches the end `a + len` with contents `ρ'` such that `R ρ ρ'`,
passing through no halting configuration.  Blocks compose sequentially and under counted loops.

`Computes f ins o b code len`: the block writes `f(ρ(ins 0), …)` into register `o`, keeps every
register `< b` other than `o`, and may use the registers `≥ b` freely.

`primrec_compiles`: for every `Nat.Primrec' f` and registers `ins`, `o < b`, such code exists.
Only correctness is proved; the compiler is applied to one fixed function in `UUniversal`.
-/
import UMachine
import Mathlib.Computability.Primrec

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ClaudeUndec
open Function

/-! ### Blocks -/

def Block (code : ℕ → List Instr) (len : ℕ) (R : (ℕ → ℕ) → (ℕ → ℕ) → Prop) : Prop :=
  (∀ a, (code a).length = len) ∧
  ∀ (P : Prog) (a : ℕ) (ρ : ℕ → ℕ), Emb P a (code a) →
    ∃ ρ', Reach P (a, ρ) (a + len, ρ') ∧ R ρ ρ'

section BlockLemmas
variable {code c₁ c₂ : ℕ → List Instr} {len l₁ l₂ : ℕ} {R R' R₁ R₂ : (ℕ → ℕ) → (ℕ → ℕ) → Prop}

theorem Block.mono (h : Block code len R) (hR : ∀ ρ ρ', R ρ ρ' → R' ρ ρ') : Block code len R' :=
  ⟨h.1, fun P a ρ hE => by
    obtain ⟨ρ', hr, hR'⟩ := h.2 P a ρ hE
    exact ⟨ρ', hr, hR ρ ρ' hR'⟩⟩

/-- Sequential composition of relocatable code. -/
def seqC (c₁ : ℕ → List Instr) (l₁ : ℕ) (c₂ : ℕ → List Instr) : ℕ → List Instr :=
  fun a => c₁ a ++ c₂ (a + l₁)

theorem Block.seq (h₁ : Block c₁ l₁ R₁) (h₂ : Block c₂ l₂ R₂) :
    Block (seqC c₁ l₁ c₂) (l₁ + l₂) (fun ρ ρ'' => ∃ ρ', R₁ ρ ρ' ∧ R₂ ρ' ρ'') := by
  refine ⟨fun a => by simp [seqC, h₁.1, h₂.1], fun P a ρ hE => ?_⟩
  have hE1 := hE.left
  have hE2 := hE.right
  rw [h₁.1] at hE2
  obtain ⟨ρ', r1, hR1⟩ := h₁.2 P a ρ hE1
  obtain ⟨ρ'', r2, hR2⟩ := h₂.2 P (a + l₁) ρ' hE2
  refine ⟨ρ'', r1.trans ?_, ρ', hR1, hR2⟩
  rwa [show a + (l₁ + l₂) = a + l₁ + l₂ by omega]

theorem Block.nil : Block (fun _ => []) 0 (fun ρ ρ' => ρ' = ρ) :=
  ⟨fun _ => rfl, fun P a ρ _ => ⟨ρ, by simpa using Reach.refl (P := P) (a, ρ), rfl⟩⟩

theorem clearB (r : ℕ) : Block (clearC r) 1 (fun ρ ρ' => ρ' = update ρ r 0) :=
  ⟨fun _ => rfl, fun _ _ ρ hE => ⟨_, clearC_run' hE ρ, rfl⟩⟩

theorem incB (r : ℕ) : Block (incC r) 1 (fun ρ ρ' => ρ' = update ρ r (ρ r + 1)) :=
  ⟨fun _ => rfl, fun _ _ ρ hE => ⟨_, incC_run hE ρ, rfl⟩⟩

theorem moveB {s d : ℕ} (hsd : s ≠ d) :
    Block (moveC s d) 2 (fun ρ ρ' => ρ' = update (update ρ d (ρ d + ρ s)) s 0) :=
  ⟨fun _ => rfl, fun _ _ ρ hE => ⟨_, moveC_run' hsd hE ρ, rfl⟩⟩

theorem dupB {s d t : ℕ} (hsd : s ≠ d) (hst : s ≠ t) (hdt : d ≠ t) :
    Block (dupC s d t) 3
      (fun ρ ρ' => ρ' = update (update (update ρ d (ρ d + ρ s)) t (ρ t + ρ s)) s 0) :=
  ⟨fun _ => rfl, fun _ _ ρ hE => ⟨_, dupC_run hsd hst hdt hE _ ρ rfl, rfl⟩⟩

/-- A counted loop with an invariant indexed by the initial contents and the number of
iterations. -/
theorem Block.loop {K lb : ℕ} {body : ℕ → List Instr} {Rb : (ℕ → ℕ) → (ℕ → ℕ) → Prop}
    (hb : Block body lb Rb) (hK : ∀ ρ ρ', Rb ρ ρ' → ρ' K = ρ K)
    (I : (ℕ → ℕ) → ℕ → (ℕ → ℕ) → Prop)
    (hI : ∀ ρ₀ i ρ ρ', I ρ₀ i ρ → ρ K ≠ 0 → Rb (update ρ K (ρ K - 1)) ρ' → I ρ₀ (i + 1) ρ') :
    Block (loopC K body lb) (lb + 2) (fun ρ ρ' => I ρ 0 ρ → I ρ (ρ K) ρ' ∧ ρ' K = 0) := by
  refine ⟨fun a => loopC_length K body lb a (hb.1 _), fun P a ρ hE => ?_⟩
  have hEb : Emb P (a + 1) (body (a + 1)) := by
    have := (hE.left (c₂ := [decI K (a + 2 + lb) (a + 1)]))
    have := this.right
    simpa using this
  classical
  by_cases h0 : I ρ 0 ρ
  · obtain ⟨ρ', hr, hI', hK'⟩ := loopC_run (hb.1 _) hE (I ρ) (fun i ρ₁ hI₁ hne => by
      obtain ⟨ρ₂, r₂, hR₂⟩ := hb.2 P (a + 1) (update ρ₁ K (ρ₁ K - 1)) hEb
      refine ⟨ρ₂, r₂, hI ρ i ρ₁ ρ₂ hI₁ hne hR₂, ?_⟩
      rw [hK _ _ hR₂]; simp) ρ h0
    exact ⟨ρ', by rwa [show a + (lb + 2) = a + 2 + lb by omega], fun _ => ⟨hI', hK'⟩⟩
  · obtain ⟨ρ', hr, -, -⟩ := loopC_run (hb.1 _) hE (fun _ _ => True) (fun i ρ₁ _ hne => by
      obtain ⟨ρ₂, r₂, hR₂⟩ := hb.2 P (a + 1) (update ρ₁ K (ρ₁ K - 1)) hEb
      refine ⟨ρ₂, r₂, trivial, ?_⟩
      rw [hK _ _ hR₂]; simp) ρ trivial
    exact ⟨ρ', by rwa [show a + (lb + 2) = a + 2 + lb by omega], fun h => absurd h h0⟩

end BlockLemmas

/-! ### Copying -/

/-- `d := s` using the temporary `t` (`s` is restored, `t` ends at `0`). -/
def copyC (s d t : ℕ) : ℕ → List Instr :=
  seqC (seqC (seqC (clearC d) 1 (clearC t)) 2 (dupC s d t)) 5 (moveC t s)

theorem copyB {s d t : ℕ} (hsd : s ≠ d) (hst : s ≠ t) (hdt : d ≠ t) :
    Block (copyC s d t) 7 (fun ρ ρ' => ρ' = update (update ρ d (ρ s)) t 0) := by
  have h := (((clearB d).seq (clearB t)).seq (dupB hsd hst hdt)).seq (moveB (Ne.symm hst))
  refine h.mono fun ρ ρ' hR => ?_
  obtain ⟨ρ3, ⟨ρ2, ⟨ρ1, rfl, rfl⟩, rfl⟩, rfl⟩ := hR
  funext x
  simp only [update_apply]
  split_ifs <;> subst_vars <;> omega

/-! ### The specification of compiled code -/

/-- `code` computes `f` from registers `ins` into register `o`; registers `≥ b` are scratch. -/
def Computes {n : ℕ} (f : List.Vector ℕ n → ℕ) (ins : Fin n → ℕ) (o b : ℕ)
    (code : ℕ → List Instr) (len : ℕ) : Prop :=
  Block code len (fun ρ ρ' => ρ' o = f (List.Vector.ofFn fun i => ρ (ins i)) ∧
    ∀ x < b, x ≠ o → ρ' x = ρ x)

/-! ### Composition: computing all arguments -/

theorem compAll {m n : ℕ} (g : Fin n → List.Vector ℕ m → ℕ) (ins : Fin m → ℕ) (b : ℕ)
    (hins : ∀ j, ins j < b)
    (hg : ∀ i : Fin n, ∀ o b', (∀ j, ins j < b') → o < b' →
      ∃ code len, Computes (g i) ins o b' code len) :
    ∀ k ≤ n, ∃ code len, Block code len (fun ρ ρ' =>
      (∀ i : Fin n, i.val < k → ρ' (b + i) = g i (List.Vector.ofFn fun j => ρ (ins j))) ∧
      ∀ x < b, ρ' x = ρ x) := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨_, _, Block.nil.mono fun ρ ρ' h => ⟨fun i hi => absurd hi (by omega), fun x _ => by
      rw [h]⟩⟩
  | succ k ih =>
    intro hk
    obtain ⟨c₁, l₁, h₁⟩ := ih (by omega)
    obtain ⟨c₂, l₂, h₂⟩ := hg ⟨k, by omega⟩ (b + k) (b + n) (fun j => by have := hins j; omega)
      (by omega)
    refine ⟨_, _, (h₁.seq h₂).mono fun ρ ρ'' hR => ?_⟩
    obtain ⟨ρ', ⟨hA, hB⟩, hC, hD⟩ := hR
    have hvec : (List.Vector.ofFn fun j => ρ' (ins j)) = List.Vector.ofFn fun j => ρ (ins j) := by
      congr 1; funext j; exact hB _ (hins j)
    refine ⟨fun i hi => ?_, fun x hx => ?_⟩
    · by_cases hik : i.val = k
      · have : i = ⟨k, by omega⟩ := Fin.ext hik
        rw [this]
        simp only
        rw [hC, hvec]
      · rw [hD _ (by omega) (by omega), hA i (by omega)]
    · rw [hD x (by omega) (by omega), hB x hx]

/-! ### The compiler -/

theorem vec_cons_ofFn {n : ℕ} (ρ : ℕ → ℕ) (y z : ℕ) (r : Fin n → ℕ) :
    (List.Vector.ofFn fun j : Fin (n + 2) => ρ ((Fin.cons y (Fin.cons z r : Fin (n + 1) → ℕ) :
      Fin (n + 2) → ℕ) j)) = ρ y ::ᵥ ρ z ::ᵥ List.Vector.ofFn fun i => ρ (r i) := by
  rfl

/-- The primitive recursion step of the compiler: `x` iterations of the body
`T := g(Y, A, rest); A := T; Y := Y + 1`, counted down in register `b`. -/
theorem prec_compiles {n : ℕ} (f : List.Vector ℕ n → ℕ) (g : List.Vector ℕ (n + 2) → ℕ)
    (ihf : ∀ (ins : Fin n → ℕ) (o b : ℕ), (∀ i, ins i < b) → o < b →
      ∃ code len, Computes f ins o b code len)
    (ihg : ∀ (ins : Fin (n + 2) → ℕ) (o b : ℕ), (∀ i, ins i < b) → o < b →
      ∃ code len, Computes g ins o b code len)
    (ins : Fin (n + 1) → ℕ) (o b : ℕ) (hins : ∀ i, ins i < b) (hob : o < b) :
    ∃ code len, Computes (fun v : List.Vector ℕ (n + 1) =>
      v.head.rec (f v.tail) fun y IH => g (y ::ᵥ IH ::ᵥ v.tail)) ins o b code len := by
  have hx := hins 0
  set rest : Fin n → ℕ := fun i => ins i.succ with hrestdef
  have hrest : ∀ i, rest i < b := fun i => hins i.succ
  obtain ⟨cf, lf, hf'⟩ := ihf rest (b + 2) (b + 5) (fun i => by have := hrest i; omega)
    (by omega)
  set insg : Fin (n + 2) → ℕ := Fin.cons (b + 1) (Fin.cons (b + 2) rest : Fin (n + 1) → ℕ)
    with hinsgdef
  obtain ⟨cg, lg, hg'⟩ := ihg insg (b + 3) (b + 5) (fun i => by
    refine Fin.cases (by simp [insg]) (fun i => ?_) i
    refine Fin.cases (by simp [insg]) (fun i => ?_) i
    simp only [insg, Fin.cons_succ]; have := hrest i; omega) (by omega)
  set V : List.Vector ℕ n → ℕ → ℕ := fun t i =>
    Nat.rec (f t) (fun y IH => g (y ::ᵥ IH ::ᵥ t)) i with hVdef
  -- the body: `T := g(Y, A, rest); A := T; Y := Y + 1`
  have hbody := ((hg'.seq (clearB (b + 2))).seq (moveB (s := b + 3) (d := b + 2) (by omega))).seq
      (incB (b + 1))
  have hbody' := hbody.mono (R' := fun ρ ρ' =>
      ρ' (b + 2) = g (List.Vector.ofFn fun i => ρ (insg i)) ∧ ρ' (b + 1) = ρ (b + 1) + 1 ∧
      ∀ x < b + 5, x ≠ b + 1 → x ≠ b + 2 → x ≠ b + 3 → ρ' x = ρ x) (by
    intro ρ ρ' hR
    obtain ⟨ρ3, ⟨ρ2, ⟨ρ1, ⟨hg1, hg2⟩, rfl⟩, rfl⟩, rfl⟩ := hR
    refine ⟨?_, ?_, fun x hx5 hx1 hx2 hx3 => ?_⟩
    · simp [hg1]
    · simp [hg2 (b + 1) (by omega) (by omega)]
    · simp [update_apply, hx1, hx2, hx3, hg2 x hx5 hx3])
  have hloop := Block.loop (K := b) hbody' (by
      intro ρ ρ' ⟨_, _, h3⟩
      exact h3 b (by omega) (by omega) (by omega) (by omega))
    (fun ρ₀ i ρ => ρ (b + 1) = i ∧ ρ (b + 2) = V (List.Vector.ofFn fun j => ρ (rest j)) i ∧
      ∀ x < b, ρ x = ρ₀ x)
    (by
      intro ρ₀ i ρ ρ' ⟨hY, hA, hP⟩ hne ⟨h1, h2, h3⟩
      have hr' : ∀ j, ρ' (rest j) = ρ (rest j) := fun j => by
        have := hrest j
        rw [h3 _ (by omega) (by omega) (by omega) (by omega)]
        simp [update_apply, show rest j ≠ b by omega]
      have hvec : (List.Vector.ofFn fun j => ρ' (rest j)) =
          List.Vector.ofFn fun j => ρ (rest j) := by
        congr 1; funext j; exact hr' j
      refine ⟨?_, ?_, fun x hx => ?_⟩
      · rw [h2]; simp [update_apply, hY]
      · rw [h1, hvec]
        have e : (List.Vector.ofFn fun i => update ρ b (ρ b - 1) (insg i)) =
            ρ (b + 1) ::ᵥ ρ (b + 2) ::ᵥ List.Vector.ofFn fun j => ρ (rest j) := by
          rw [vec_cons_ofFn]
          simp only [update_apply, show b + 1 ≠ b by omega, show b + 2 ≠ b by omega, if_false]
          congr 3
          funext j
          have := hrest j
          simp [show rest j ≠ b by omega]
        rw [e, hY, hA]
      · rw [h3 x (by omega) (by omega) (by omega) (by omega)]
        simp [update_apply, show x ≠ b by omega, hP x hx])
  have h := (((((copyB (s := ins 0) (d := b) (t := b + 4) (by omega) (by omega) (by omega)).seq
    (clearB (b + 1))).seq hf').seq hloop).seq (clearB o)).seq
      (moveB (s := b + 2) (d := o) (by omega))
  refine ⟨_, _, h.mono fun ρ ρ' hR => ?_⟩
  obtain ⟨ρ5, ⟨ρ4, ⟨ρ3, ⟨ρ2, ⟨ρ1, h1, h2⟩, ⟨hf1, hf2⟩⟩, hL⟩, h5⟩, h6⟩ := hR
  -- before the loop
  have hρ2 : ∀ x < b, ρ2 x = ρ x := fun x hx => by
    rw [h2, h1]; simp [update_apply, show x ≠ b + 1 by omega, show x ≠ b + 4 by omega,
      show x ≠ b by omega]
  have hK3 : ρ3 b = ρ (ins 0) := by
    rw [hf2 b (by omega) (by omega), h2, h1]; simp [update_apply]
  have hY3 : ρ3 (b + 1) = 0 := by
    rw [hf2 (b + 1) (by omega) (by omega), h2]; simp [update_apply]
  have hρ3 : ∀ x < b, ρ3 x = ρ x := fun x hx => by
    rw [hf2 x (by omega) (by omega), hρ2 x hx]
  have hvec3 : (List.Vector.ofFn fun j => ρ3 (rest j)) = List.Vector.ofFn fun j => ρ (rest j) := by
    congr 1; funext j; exact hρ3 _ (hrest j)
  have hvec2 : (List.Vector.ofFn fun j => ρ2 (rest j)) = List.Vector.ofFn fun j => ρ (rest j) := by
    congr 1; funext j; exact hρ2 _ (hrest j)
  obtain ⟨⟨-, hA4, hP4⟩, -⟩ := hL ⟨hY3, by rw [hf1, hvec2, hvec3]; rfl, fun _ _ => rfl⟩
  have hvec4 : (List.Vector.ofFn fun j => ρ4 (rest j)) = List.Vector.ofFn fun j => ρ (rest j) := by
    congr 1; funext j; rw [hP4 _ (hrest j), hρ3 _ (hrest j)]
  refine ⟨?_, fun x hxb hxo => ?_⟩
  · have e1 : ρ' o = ρ4 (b + 2) := by
      rw [h6, h5]
      simp [update_apply, show o ≠ b + 2 by omega, show b + 2 ≠ o by omega]
    rw [e1, hA4, hvec4, hK3]
    simp only [List.Vector.head_ofFn, List.Vector.tail_ofFn]
    rfl
  · rw [h6, h5]
    simp only [update_apply, show x ≠ b + 2 by omega, hxo, if_false]
    rw [hP4 x hxb, hρ3 x hxb]

/-- **Every primitive recursive function is computed by counter-machine code.** -/
theorem primrec_compiles : ∀ {n : ℕ} {f : List.Vector ℕ n → ℕ}, Nat.Primrec' f →
    ∀ (ins : Fin n → ℕ) (o b : ℕ), (∀ i, ins i < b) → o < b →
      ∃ code len, Computes f ins o b code len := by
  intro n f hf
  induction hf with
  | zero =>
    intro ins o b _ hob
    exact ⟨_, _, (clearB o).mono fun ρ ρ' h => by
      subst h; exact ⟨by simp, fun x _ hx => by simp [update_apply, hx]⟩⟩
  | succ =>
    intro ins o b hins hob
    have hx := hins 0
    have h := (((copyB (s := ins 0) (d := b) (t := b + 1) (by omega) (by omega) (by omega)).seq
      (incB b)).seq (clearB o)).seq (moveB (s := b) (d := o) (by omega))
    refine ⟨_, _, h.mono fun ρ ρ' hR => ?_⟩
    obtain ⟨ρ3, ⟨ρ2, ⟨ρ1, rfl, rfl⟩, rfl⟩, rfl⟩ := hR
    refine ⟨?_, fun x hxb hxo => ?_⟩
    · simp only [List.Vector.head_ofFn, update_apply]
      split_ifs <;> omega
    · simp only [update_apply]
      split_ifs <;> omega
  | get i =>
    intro ins o b hins hob
    have hx := hins i
    have h := ((copyB (s := ins i) (d := b) (t := b + 1) (by omega) (by omega) (by omega)).seq
      (clearB o)).seq (moveB (s := b) (d := o) (by omega))
    refine ⟨_, _, h.mono fun ρ ρ' hR => ?_⟩
    obtain ⟨ρ2, ⟨ρ1, rfl, rfl⟩, rfl⟩ := hR
    refine ⟨?_, fun x hxb hxo => ?_⟩
    · simp only [List.Vector.get_ofFn, update_apply]
      split_ifs <;> omega
    · simp only [update_apply]
      split_ifs <;> omega
  | @comp m n f g _ _ ihf ihg =>
    intro ins o b hins hob
    obtain ⟨c₁, l₁, h₁⟩ := compAll g ins b hins (fun i o b' h1 h2 => ihg i ins o b' h1 h2) n le_rfl
    obtain ⟨c₂, l₂, h₂⟩ := ihf (fun i => b + i) o (b + n)
      (fun i => by show b + i.val < b + n; have := i.2; omega)
      (by omega)
    refine ⟨_, _, (h₁.seq h₂).mono fun ρ ρ'' hR => ?_⟩
    obtain ⟨ρ', ⟨hA, hB⟩, hC, hD⟩ := hR
    refine ⟨?_, fun x hx hxo => ?_⟩
    · rw [hC]
      congr 1
      apply List.Vector.ext
      intro i
      simp only [List.Vector.get_ofFn]
      exact hA i i.2
    · rw [hD x (by omega) hxo, hB x hx]
  | @prec n f g _ _ ihf ihg =>
    intro ins o b hins hob
    exact prec_compiles f g ihf ihg ins o b hins hob

end ClaudeUndec
