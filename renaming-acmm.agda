module renaming-acmm where

open import Function as F hiding (_∋_ ; _$_)
open import Relation.Binary.PropositionalEquality as PEq using (_≡_)

open import lambda-fg
open import semantics

Renaming : Semantics Var→Val Val→Trm
Renaming = syntactic 𝓥ar₀

infix 4 _*-Var_

_*-Var_ : ∀ {f} {Γ Δ} → (inc : Γ ⊆ Δ) →
          {σ : Ty} (t : Exp {f} σ Γ) → Exp {f} σ Δ
inc *-Var t = sem inc t where open Eval Renaming

th^Val : ∀ {σ} → Thinnable (Val σ)
th^Val t ρ = ρ *-Var t

ren : ∀ {f} {Γ Δ} {σ} → Exp {f} σ Γ → Γ ⊆ Δ → Exp {f} σ Δ
ren E r = r *-Var E

-- Syntactic Sugar

-- We need spine applications. The right way to formalise this is, as ever, on
-- values, and then on terms (?). To start with, we therefore need clausal
-- form for types.

-- We need a Trm-level application (to a Val), for app-cxt-sim and
-- subsequently.

-- this is Craig's version: much smoother!
Val→Spine : ∀ {Γ} {σ τ} (V : Val σ Γ) → Trm τ (Γ ∙ (σ `→ τ))
Val→Spine V = val₀ `$ (weak *-Var V)

appT : ∀ {Γ} {σ τ} (M : Trm (σ `→ τ) Γ) → (V : Val σ Γ) → Trm τ Γ
appT M V = `let M (Val→Spine V)

-- Proofs about renaming

ext₀^Var-ext₀ : ∀ {Γ} {σ} → {ρ : Γ ⊆ Γ} → (∀ {τ} v → var ρ {τ} v ≡ v) →
 ∀ {τ} v → var (pop! {σ} {Γ} ρ) {τ} v ≡ v
ext₀^Var-ext₀ {Γ} {σ} {ρ} eq =
  [ P ][ PEq.refl ,,,  PEq.cong su ∘ eq ]
 where P = λ {τ} v → var (pop! {σ} {Γ} ρ) {τ} v ≡ v

ι^Var-lemma-aux : {Γ : Cx} {σ : Ty} {ρ : Γ ⊆ Γ}
             (prf : {τ : Ty} (v : Var τ Γ) → var ρ {τ} v ≡ v) →
             {cbv : CBV} (E : Exp {cbv} σ Γ) →
             (ρ *-Var E) ≡ E
ι^Var-lemma-aux prf  (`var v)
 rewrite prf v             = PEq.refl
ι^Var-lemma-aux prf   (`b b)    = PEq.refl
ι^Var-lemma-aux prf   (`λ M)
 rewrite ι^Var-lemma-aux (ext₀^Var-ext₀ prf) M    = PEq.refl
ι^Var-lemma-aux prf  (`val V)
 rewrite ι^Var-lemma-aux prf V  = PEq.refl
ι^Var-lemma-aux prf  (F `$ A)
 rewrite ι^Var-lemma-aux prf F | ι^Var-lemma-aux prf A = PEq.refl
ι^Var-lemma-aux prf (`if B L R)
  rewrite ι^Var-lemma-aux prf B | ι^Var-lemma-aux prf L |
          ι^Var-lemma-aux prf R = PEq.refl
ι^Var-lemma-aux prf  (`let M N)
  rewrite ι^Var-lemma-aux prf M |
          ι^Var-lemma-aux (ext₀^Var-ext₀ prf) N = PEq.refl

ι^Var-lemma : ∀ {f} {Γ} {σ} → (E : Exp {f} σ Γ) → (ι^Var *-Var E) ≡ E
ι^Var-lemma = ι^Var-lemma-aux {ρ = ι^Var} (λ v → PEq.refl)

ι^Var₀-lemma : ∀ {f} {σ} → (ρ : ε ⊆ ε) (E : Exp₀ {f} σ) → (ρ *-Var E) ≡ E
ι^Var₀-lemma ρ = ι^Var-lemma-aux {ρ = ρ} (λ ())
