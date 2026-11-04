/-
Claude, 27 Sep 2026.  Undecidability, part G1: the reduction is primitive recursive.

Machines (`Prog`) and normalized sentences (`Sentence`) are built from `ℕ`, `Bool`, `Unit`,
products, sums and lists, so they carry Mathlib's standard `Primcodable` coding.  This file proves
(`Primrec` in Mathlib's sense, which implies `Computable`):

* `theta_primrec : Primrec theta` (the sentence `θ_M` is computed from `M` alone);
* `conj_primrec ψ : Primrec (conj ψ)` (conjunction with a fixed witness);
* `univProg_primrec : Primrec univProg`.
-/
import UUniversal
import UCounter

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ClaudeUndec
open Primrec

/-! ### Building blocks -/

section Blocks
variable {α : Type} [Primcodable α]

theorem p_rel {R : α → ℕ} {args : α → List ℕ} (hR : Primrec R) (ha : Primrec args) :
    Primrec fun a => (Atom.rel (R a) (args a) : Atom) := sumInl.comp (hR.pair ha)

theorem p_graph {f : α → ℕ} {args : α → List ℕ} {out : α → ℕ} (hf : Primrec f)
    (ha : Primrec args) (ho : Primrec out) :
    Primrec fun a => (Atom.graph (f a) (args a) (out a) : Atom) :=
  sumInr.comp (sumInl.comp ((hf.pair ha).pair ho))

theorem p_eq {i j : α → ℕ} (hi : Primrec i) (hj : Primrec j) :
    Primrec fun a => (Atom.eq (i a) (j a) : Atom) := sumInr.comp (sumInr.comp (hi.pair hj))

theorem p_pos {x : α → Atom} (h : Primrec x) : Primrec fun a => pos (x a) := (const true).pair h
theorem p_neg {x : α → Atom} (h : Primrec x) : Primrec fun a => neg (x a) := (const false).pair h

theorem p_cons {β : Type} [Primcodable β] {x : α → β} {l : α → List β} (hx : Primrec x)
    (hl : Primrec l) : Primrec fun a => x a :: l a := list_cons.comp hx hl

theorem p_app {β : Type} [Primcodable β] {l₁ l₂ : α → List β} (h₁ : Primrec l₁)
    (h₂ : Primrec l₂) : Primrec fun a => l₁ a ++ l₂ a := list_append.comp h₁ h₂

theorem p_add {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) : Primrec fun a => f a + g a :=
  nat_add.comp hf hg

theorem p_qA {ℓ i : α → ℕ} (hℓ : Primrec ℓ) (hi : Primrec i) :
    Primrec fun a => qA (ℓ a) (i a) :=
  p_rel (p_add (const 1) hℓ) (p_cons hi (const []))

theorem p_cOf {r c t : α → ℕ} (hr : Primrec r) (hc : Primrec c) (ht : Primrec t) :
    Primrec fun a => cOf (r a) (c a) (t a) :=
  p_graph (p_add (const 3) hr) (p_cons ht (const [])) hc

theorem p_pre {ℓ : α → ℕ} (hℓ : Primrec ℓ) : Primrec fun a => pre (ℓ a) :=
  p_cons (const _) (p_cons (const _) (p_cons (p_neg (p_qA hℓ (const 0))) (const _)))

/-- Mapping a filtered list is a `flatMap`. -/
theorem map_filter_eq_flatMap {β γ : Type} (l : List β) (p : β → Bool) (f : β → γ) :
    (l.filter p).map f = l.flatMap fun x => if p x then [f x] else [] := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases hx : p x = true
    · simp [List.filter_cons, hx, ih]
    · simp [List.filter_cons, hx, ih]

end Blocks

/-! ### The counters and the signature of `θ_M` -/

theorem instrCnt_primrec : Primrec Prog.instrCnt :=
  (sumCasesOn Primrec.id (fst.comp snd).to₂
    (sumCasesOn snd (fst.comp snd).to₂ (const 0).to₂).to₂).of_eq fun i => by
      rcases i with ⟨_, _⟩ | ⟨_, _, _⟩ | _ <;> rfl

theorem ncnt_primrec : Primrec Prog.ncnt :=
  (p_add (list_foldr (list_map Primrec.id (instrCnt_primrec.comp snd).to₂) (const 0)
    (nat_max.comp (fst.comp snd) (snd.comp snd)).to₂) (const 1)).of_eq fun P => by
      simp only [Prog.ncnt]; rfl

theorem replicate_eq_map (k : ℕ) (x : ℕ) : List.replicate k x = (List.range k).map fun _ => x := by
  rw [List.map_const', List.length_range]

theorem thRels_primrec : Primrec thRels :=
  (p_cons (const 2) (list_map (list_range.comp (p_add list_length (const 1))) (const 1).to₂)).of_eq
    fun P => by simp only [thRels, replicate_eq_map]

theorem thFuns_primrec : Primrec thFuns :=
  (p_cons (const 0) (p_cons (const 0) (p_cons (const 1)
    (list_map (list_range.comp ncnt_primrec) (const 1).to₂)))).of_eq
    fun P => by simp only [thFuns, replicate_eq_map]

/-! ### The base clauses -/

theorem isHalt_primrecPred : PrimrecPred fun x : Prog × ℕ => Prog.IsHaltSt x.1 x.2 :=
  PrimrecPred.or (nat_le.comp (list_length.comp fst) snd)
    (Primrec.eq.comp (list_getElem?.comp fst snd) (const (some (Sum.inr (Sum.inr ())))))

theorem baseClauses_primrec : Primrec baseClauses := by
  have hlen : Primrec fun P : Prog => P.length + 1 := p_add list_length (const 1)
  have h9 : Primrec fun P : Prog => (List.range (P.length + 1)).map (fun ℓ => pos (qA ℓ 0)) :=
    list_map (list_range.comp hlen) (p_pos (p_qA snd (const 0))).to₂
  have hin : Primrec fun z : (Prog × ℕ) × ℕ =>
      if z.1.2 < z.2 then some [neg (qA z.1.2 0), neg (qA z.2 0)] else none :=
    Primrec.ite (nat_lt.comp (snd.comp fst) snd)
      (option_some.comp (p_cons (p_neg (p_qA (snd.comp fst) (const 0)))
        (p_cons (p_neg (p_qA snd (const 0))) (const []))))
      (const none)
  have hX : Primrec fun P : Prog => (List.range (P.length + 1)).flatMap (fun a =>
      (List.range (P.length + 1)).filterMap (fun b =>
        if a < b then some [neg (qA a 0), neg (qA b 0)] else none)) := by
    refine list_flatMap (list_range.comp hlen) ?_
    exact (listFilterMap (list_range.comp (hlen.comp fst)) hin.to₂).to₂
  have hY : Primrec fun P : Prog => (List.range P.ncnt).map
      (fun r => [neg (isO 1), neg (cOf r 3 1), pos (Atom.eq 3 1)]) :=
    list_map (list_range.comp ncnt_primrec)
      (p_cons (const _) (p_cons (p_neg (p_cOf snd (const 3) (const 1))) (const _))).to₂
  have hZ : Primrec fun P : Prog =>
      ((List.range (P.length + 1)).filter (fun ℓ => decide (Prog.IsHaltSt P ℓ))).map
        (fun ℓ => [neg (qA ℓ 0)]) := by
    have hz : Primrec fun z : Prog × ℕ =>
        if Prog.IsHaltSt z.1 z.2 then [[neg (qA z.2 0)]] else ([] : List Clause) :=
      Primrec.ite isHalt_primrecPred (p_cons (p_cons (p_neg (p_qA snd (const 0))) (const []))
        (const [])) (const [])
    refine (list_flatMap (list_range.comp hlen) hz.to₂).of_eq fun P => ?_
    rw [map_filter_eq_flatMap]
    congr 1
    funext ℓ
    by_cases h : Prog.IsHaltSt P ℓ <;> simp [h]
  have h10 : Primrec fun P : Prog =>
      [[neg (ltA 0 0)],
       [neg (ltA 0 7), neg (ltA 7 2), pos (ltA 0 2)],
       [pos (ltA 0 2), pos (Atom.eq 0 2), pos (ltA 2 0)],
       [neg (isO 1), pos (Atom.eq 0 1), pos (ltA 1 0)],
       [neg (isE 1), pos (Atom.eq 0 1), pos (ltA 0 1)],
       [neg (isE 1), neg (sOf 2 1), pos (Atom.eq 2 1)],
       [neg (isE 1), pos (Atom.eq 0 1), neg (sOf 2 0), pos (ltA 0 2)],
       [neg (isE 1), pos (Atom.eq 0 1), neg (sOf 2 0), neg (ltA 0 7), neg (ltA 7 2)],
       (List.range (P.length + 1)).map (fun ℓ => pos (qA ℓ 0)),
       [neg (isO 1), pos (qA 0 1)]] :=
    p_cons (const _) (p_cons (const _) (p_cons (const _) (p_cons (const _) (p_cons (const _)
      (p_cons (const _) (p_cons (const _) (p_cons (const _) (p_cons h9 (const _)))))))))
  exact (p_app (p_app (p_app h10 hX) hY) hZ).of_eq fun P => rfl

/-! ### The transition clauses -/

theorem sameClauses_primrec {α : Type} [Primcodable α] {P : α → Prog} {ℓ r : α → ℕ}
    {extra : α → Clause} (hP : Primrec P) (hℓ : Primrec ℓ) (hr : Primrec r)
    (he : Primrec extra) :
    Primrec fun a => sameClauses (P a) (ℓ a) (r a) (extra a) := by
  have hb : Primrec fun z : α × ℕ => if z.2 = r z.1 then ([] : List Clause) else
      [pre (ℓ z.1) ++ extra z.1 ++ [neg (cOf z.2 6 0), pos (cOf z.2 6 2)]] :=
    Primrec.ite (Primrec.eq.comp snd (hr.comp fst)) (const [])
      (p_cons (p_app (p_app (p_pre (hℓ.comp fst)) (he.comp fst))
        (p_cons (p_neg (p_cOf snd (const 6) (const 0)))
          (p_cons (p_pos (p_cOf snd (const 6) (const 2))) (const [])))) (const []))
  refine (list_flatMap (list_range.comp (ncnt_primrec.comp hP)) hb.to₂).of_eq fun a => ?_
  simp only [sameClauses]
  rw [map_filter_eq_flatMap]
  congr 1
  funext r'
  by_cases h : r' = r a <;> simp [h]

section TransPrim
variable {β : Type} [Primcodable β]

/-- A literal list headed by the transition premise. -/
theorem p_preApp {ℓ : β → ℕ} {rest : β → Clause} (hℓ : Primrec ℓ) (hrest : Primrec rest) :
    Primrec fun a => pre (ℓ a) ++ rest a := p_app (p_pre hℓ) hrest

end TransPrim

set_option maxHeartbeats 4000000 in
theorem transClauses_primrec :
    Primrec fun x : (Prog × ℕ) × Instr => transClauses x.1.1 x.1.2 x.2 := by
  -- the increment branch, as a function of `(x, (r, ℓ'))`
  have hinc : Primrec₂ fun (x : (Prog × ℕ) × Instr) (y : ℕ × ℕ) =>
      [ pre x.1.2 ++ [neg (cOf y.1 3 0), neg (Atom.eq 3 1)],
        pre x.1.2 ++ [neg (cOf y.1 3 0), neg (sOf 4 3), pos (cOf y.1 4 2)],
        pre x.1.2 ++ [pos (qA (Prog.norm x.1.1 y.2) 2)] ] ++ sameClauses x.1.1 x.1.2 y.1 [] := by
    have hℓ : Primrec fun z : ((Prog × ℕ) × Instr) × (ℕ × ℕ) => z.1.1.2 := snd.comp (fst.comp fst)
    have hP : Primrec fun z : ((Prog × ℕ) × Instr) × (ℕ × ℕ) => z.1.1.1 :=
      fst.comp (fst.comp fst)
    have hr : Primrec fun z : ((Prog × ℕ) × Instr) × (ℕ × ℕ) => z.2.1 := fst.comp snd
    have hnorm : Primrec fun z : ((Prog × ℕ) × Instr) × (ℕ × ℕ) => Prog.norm z.1.1.1 z.2.2 :=
      nat_min.comp (snd.comp snd) (list_length.comp hP)
    have c1 := p_preApp hℓ (p_cons (p_neg (p_cOf hr (const 3) (const 0))) (const [neg (Atom.eq 3 1)]))
    have c2 := p_preApp hℓ (p_cons (p_neg (p_cOf hr (const 3) (const 0)))
      (p_cons (const (neg (sOf 4 3))) (p_cons (p_pos (p_cOf hr (const 4) (const 2))) (const []))))
    have c3 := p_preApp hℓ (p_cons (p_pos (p_qA hnorm (const 2))) (const []))
    exact p_app (p_cons c1 (p_cons c2 (p_cons c3 (const []))))
      (sameClauses_primrec hP hℓ hr (const []))
  -- the decrement branch, as a function of `(x, (r, ℓ₀, ℓ₁))`
  have hdec : Primrec₂ fun (x : (Prog × ℕ) × Instr) (y : ℕ × ℕ × ℕ) =>
      [ pre x.1.2 ++ [neg (isO 5), neg (cOf y.1 3 0), neg (Atom.eq 3 5), pos (cOf y.1 3 2)],
        pre x.1.2 ++ [neg (isO 5), neg (cOf y.1 3 0), neg (Atom.eq 3 5),
          pos (qA (Prog.norm x.1.1 y.2.1) 2)],
        pre x.1.2 ++ [neg (isO 5), neg (cOf y.1 3 0), pos (Atom.eq 3 5), neg (cOf y.1 6 2),
          pos (ltA 6 3)],
        pre x.1.2 ++ [neg (isO 5), neg (cOf y.1 3 0), pos (Atom.eq 3 5), neg (cOf y.1 6 2),
          neg (sOf 4 6), pos (Atom.eq 4 3)],
        pre x.1.2 ++ [neg (isO 5), neg (cOf y.1 3 0), pos (Atom.eq 3 5),
          pos (qA (Prog.norm x.1.1 y.2.2) 2)] ] ++
      sameClauses x.1.1 x.1.2 y.1 [neg (isO 5), neg (cOf y.1 3 0), neg (Atom.eq 3 5)] ++
      sameClauses x.1.1 x.1.2 y.1 [neg (isO 5), neg (cOf y.1 3 0), pos (Atom.eq 3 5)] := by
    have hℓ : Primrec fun z : ((Prog × ℕ) × Instr) × (ℕ × ℕ × ℕ) => z.1.1.2 :=
      snd.comp (fst.comp fst)
    have hP : Primrec fun z : ((Prog × ℕ) × Instr) × (ℕ × ℕ × ℕ) => z.1.1.1 :=
      fst.comp (fst.comp fst)
    have hr : Primrec fun z : ((Prog × ℕ) × Instr) × (ℕ × ℕ × ℕ) => z.2.1 := fst.comp snd
    have hn0 : Primrec fun z : ((Prog × ℕ) × Instr) × (ℕ × ℕ × ℕ) => Prog.norm z.1.1.1 z.2.2.1 :=
      nat_min.comp (fst.comp (snd.comp snd)) (list_length.comp hP)
    have hn1 : Primrec fun z : ((Prog × ℕ) × Instr) × (ℕ × ℕ × ℕ) => Prog.norm z.1.1.1 z.2.2.2 :=
      nat_min.comp (snd.comp (snd.comp snd)) (list_length.comp hP)
    have hC3 := p_neg (p_cOf hr (const 3) (const 0))
    have c1 := p_preApp hℓ (p_cons (const (neg (isO 5))) (p_cons hC3
      (p_cons (const (neg (Atom.eq 3 5))) (p_cons (p_pos (p_cOf hr (const 3) (const 2)))
        (const [])))))
    have c2 := p_preApp hℓ (p_cons (const (neg (isO 5))) (p_cons hC3
      (p_cons (const (neg (Atom.eq 3 5))) (p_cons (p_pos (p_qA hn0 (const 2))) (const [])))))
    have c3 := p_preApp hℓ (p_cons (const (neg (isO 5))) (p_cons hC3
      (p_cons (const (pos (Atom.eq 3 5))) (p_cons (p_neg (p_cOf hr (const 6) (const 2)))
        (p_cons (const (pos (ltA 6 3))) (const []))))))
    have c4 := p_preApp hℓ (p_cons (const (neg (isO 5))) (p_cons hC3
      (p_cons (const (pos (Atom.eq 3 5))) (p_cons (p_neg (p_cOf hr (const 6) (const 2)))
        (p_cons (const (neg (sOf 4 6))) (p_cons (const (pos (Atom.eq 4 3))) (const [])))))))
    have c5 := p_preApp hℓ (p_cons (const (neg (isO 5))) (p_cons hC3
      (p_cons (const (pos (Atom.eq 3 5))) (p_cons (p_pos (p_qA hn1 (const 2))) (const [])))))
    have e0 := p_cons (const (neg (isO 5))) (p_cons hC3 (p_cons (const (neg (Atom.eq 3 5)))
      (const [])))
    have e1 := p_cons (const (neg (isO 5))) (p_cons hC3 (p_cons (const (pos (Atom.eq 3 5)))
      (const [])))
    exact p_app (p_app (p_cons c1 (p_cons c2 (p_cons c3 (p_cons c4 (p_cons c5 (const []))))))
      (sameClauses_primrec hP hℓ hr e0)) (sameClauses_primrec hP hℓ hr e1)
  refine (sumCasesOn snd hinc (sumCasesOn snd (hdec.comp (fst.comp fst) snd).to₂
    (const []).to₂).to₂).of_eq fun x => ?_
  rcases x with ⟨⟨P, ℓ⟩, ⟨r, ℓ'⟩ | ⟨r, ℓ₀, ℓ₁⟩ | u⟩ <;> rfl

theorem theta_primrec : Primrec theta := by
  have htrans : Primrec fun P : Prog => (List.range P.length).flatMap
      (fun ℓ => match P[ℓ]? with | some i => transClauses P ℓ i | none => []) := by
    refine list_flatMap (list_range.comp list_length) ?_
    refine (option_casesOn (list_getElem?.comp fst snd) (const [])
      (transClauses_primrec.comp (fst.pair snd)).to₂).to₂.of_eq fun P ℓ => ?_
    rcases h : P[ℓ]? with _ | i <;> simp [h]
  exact ((thRels_primrec.pair thFuns_primrec).pair (p_app baseClauses_primrec htrans)).of_eq
    fun P => rfl

/-! ### Conjunction with a fixed sentence -/

theorem atomShift_primrec (dR dF : ℕ) : Primrec (Atom.shift dR dF) :=
  (sumCasesOn Primrec.id (sumInl.comp ((p_add (const dR) (fst.comp snd)).pair (snd.comp snd))).to₂
    (sumCasesOn snd (sumInr.comp (sumInl.comp (((p_add (const dF) (fst.comp (fst.comp snd))).pair
      (snd.comp (fst.comp snd))).pair (snd.comp snd)))).to₂
      (sumInr.comp (sumInr.comp snd)).to₂).to₂).of_eq fun a => by
    rcases a with ⟨_, _⟩ | ⟨⟨_, _⟩, _⟩ | ⟨_, _⟩ <;> rfl

theorem conj_primrec (ψ : Sentence) : Primrec (conj ψ) := by
  have hshift : Primrec (Clause.shift ψ.rels.length ψ.funs.length) :=
    list_map Primrec.id ((fst.comp snd).pair ((atomShift_primrec _ _).comp (snd.comp snd))).to₂
  exact ((p_app (const ψ.rels) (fst.comp fst) |>.pair (p_app (const ψ.funs) (snd.comp fst))).pair
    (p_app (const ψ.clauses) (list_map snd (hshift.comp snd).to₂))).of_eq fun φ => rfl

/-! ### The universal machine -/

theorem univProg_primrec : Primrec univProg :=
  (p_app (const univPre) (p_app (list_map (list_range) ((sumInl.comp
    ((const 0).pair (p_add (p_add (const (hLen + 4)) snd) (const 1))))).to₂)
    (const [decI 3 1 1]))).of_eq fun _ => rfl

end ClaudeUndec
