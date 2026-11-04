/-
Claude, 27 Sep 2026.  Undecidability, part K2: the guarded join with a fixed first block is
primitive recursive (`join_primrec`), via `nvars_primrec` for the fresh guard variable.
-/
import UComputable
import UJoin

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace ClaudeUndec
open Primrec

theorem vars_primrec : Primrec Atom.vars :=
  (sumCasesOn Primrec.id (snd.comp snd).to₂
    (sumCasesOn snd (list_cons.comp (snd.comp snd) (snd.comp (fst.comp snd))).to₂
      (list_cons.comp (fst.comp snd) (list_cons.comp (snd.comp snd) (const []))).to₂).to₂).of_eq
    fun a => by rcases a with ⟨_, _⟩ | ⟨⟨_, _⟩, _⟩ | ⟨_, _⟩ <;> rfl

theorem nvars_primrec : Primrec nvars :=
  (nat_add.comp (list_foldr (list_flatMap Primrec.id (vars_primrec.comp (snd.comp snd)).to₂)
    (const 0) (nat_max.comp (fst.comp snd) (snd.comp snd)).to₂) (const 1)).of_eq fun _ => rfl

section Guards
variable {α : Type} [Primcodable α]

theorem p_guardN {z : α → ℕ} {c : α → Clause} (hz : Primrec z) (hc : Primrec c) :
    Primrec fun a => guardN (z a) (c a) :=
  p_cons ((const false).pair (p_rel hz (p_cons (nvars_primrec.comp hc) (const [])))) hc

theorem p_guardP {z : α → ℕ} {c : α → Clause} (hz : Primrec z) (hc : Primrec c) :
    Primrec fun a => guardP (z a) (c a) :=
  p_cons ((const true).pair (p_rel hz (p_cons (nvars_primrec.comp hc) (const [])))) hc

end Guards

/-- The numerical parameters of the translation (`k`, `s`, `D` and the stabilization threshold
`n₀ = kD + s + 1` of `template`) are primitive recursive functions of the sentence. -/
theorem templateParams_primrec :
    Primrec fun φ : Sentence => (maxVArity φ, axSupp φ, degD φ,
      maxVArity φ * degD φ + axSupp φ + 1) := by
  have hfold : Primrec fun l : List ℕ => l.foldr max 0 :=
    (list_foldr Primrec.id (const 0) (nat_max.comp (fst.comp snd) (snd.comp snd)).to₂).of_eq
      fun _ => rfl
  have hk : Primrec fun φ : Sentence => maxVArity φ :=
    (p_add (p_add (hfold.comp (fst.comp fst)) (hfold.comp (snd.comp fst))) (const 1)).of_eq
      fun _ => rfl
  have hw : Primrec fun φ : Sentence => maxWidth φ :=
    (hfold.comp (list_map snd (list_length.comp snd).to₂)).of_eq fun _ => rfl
  have hv : Primrec fun φ : Sentence => maxNvars φ :=
    (hfold.comp (list_map snd (nvars_primrec.comp snd).to₂)).of_eq fun _ => rfl
  have hs : Primrec fun φ : Sentence => axSupp φ :=
    (p_add (p_add hk (const 1)) hv).of_eq fun _ => rfl
  have hD : Primrec fun φ : Sentence => degD φ := (p_add hw (const 2)).of_eq fun _ => rfl
  exact hk.pair (hs.pair (hD.pair (p_add (p_add (nat_mul.comp hk hD) hs) (const 1))))

/-- The guarded join with a fixed first block is primitive recursive. -/
theorem join_primrec (A : Sentence) : Primrec (join A) := by
  have hshift : Primrec (Clause.shift A.rels.length A.funs.length) :=
    list_map Primrec.id ((fst.comp snd).pair ((atomShift_primrec _ _).comp (snd.comp snd))).to₂
  have hz : Primrec fun q : Sentence × Clause => A.rels.length + q.1.rels.length :=
    p_add (const _) (list_length.comp (fst.comp (fst.comp fst)))
  exact ((p_app (p_app (const A.rels) (fst.comp fst)) (const [1]) |>.pair
      (p_app (const A.funs) (snd.comp fst))).pair
    (p_app (list_map (const A.clauses) (p_guardN hz snd).to₂)
      (list_map (list_map snd (hshift.comp snd).to₂) (p_guardP hz snd).to₂))).of_eq fun B => rfl

end ClaudeUndec
