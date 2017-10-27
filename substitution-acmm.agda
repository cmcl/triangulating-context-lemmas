{--------------------------------------------------------}
{-- Substitution is a syntactic instance of Semantics. --}
{--------------------------------------------------------}
module substitution-acmm where

open import Function as F hiding (_∋_ ; _$_)

open import tri-prelude
open import lambda-fg
open import semantics-acmm
open import renaming-acmm

-- Value substitution

𝓥al : Model Val
𝓥al = mkModel th^Val

ext^Env : ∀ {Γ Δ Θ} {σ} → (Γ ⊨ Δ) → (Δ ⊆ Θ) → (Val σ Θ) → Γ ∙ σ ⊨ Θ
ext^Env ρ inc u = ext ρ inc u where open Thin 𝓥al

𝓥al₀ : Model₀ 𝓥al
𝓥al₀ = mkVar₀ val₀

ext₀^Env : ∀ {σ} {Γ Δ} → (Γ ⊨ Δ) → (Γ ∙ σ) ⊨ (Δ ∙ σ)
ext₀^Env = ext₀ where open Ext₀ 𝓥al₀

Val→Val : Morphism 𝓥al Val
Val→Val = ι^Inj

Substitution : Semantics Val→Val Val→Trm
Substitution = syntactic 𝓥al₀

infix 4 _*-Val_

_*-Val_ : {f : CBV} {Γ Δ : Cx} (ρ : Γ ⊨ Δ) →
          {σ : Ty} (t : Exp {f} σ Γ) → Exp {f} σ Δ
ρ *-Val e = sem ρ e where open Eval Substitution

subst : ∀ {f} {Γ Δ} {σ} → Exp {f} σ Γ → Γ ⊨ Δ → Exp {f} σ Δ
subst e ρ = ρ *-Val e

ext₀^Env-ext₀ : ∀ {Γ} {σ} → {ρ : Γ ⊨ Γ} → (∀ {τ} v → var ρ {τ} v ≡ `var v) →
 ∀ {τ} v → var (ext₀^Env {σ} {Γ} ρ) {τ} v ≡ `var v
ext₀^Env-ext₀ {Γ} {σ} {ρ} eq =
  [ P ][ PEq.refl ,,,  PEq.cong (weak *-Var_) ∘ eq ]
 where P = λ {τ} v → var (ext₀^Env {σ} {Γ} ρ) {τ} v ≡ `var v

ι^Env-lemma-aux : {Γ : Cx} {σ : Ty} {ρ : Γ ⊨ Γ}
             (prf : {τ : Ty} (v : Var τ Γ) → var ρ {τ} v ≡ `var v) →
             {cbv : CBV} (E : Exp {cbv} σ Γ) →
             (ρ *-Val E) ≡ E
ι^Env-lemma-aux prf  (`var v)
 rewrite prf v             = PEq.refl
ι^Env-lemma-aux prf   (`b b)    = PEq.refl
ι^Env-lemma-aux prf   (`λ M)
 rewrite ι^Env-lemma-aux (ext₀^Env-ext₀ prf) M    = PEq.refl
ι^Env-lemma-aux prf  (`val V)
 rewrite ι^Env-lemma-aux prf V  = PEq.refl
ι^Env-lemma-aux prf  (F `$ A)
 rewrite ι^Env-lemma-aux prf F | ι^Env-lemma-aux prf A = PEq.refl
ι^Env-lemma-aux prf (`if B L R)
  rewrite ι^Env-lemma-aux prf B | ι^Env-lemma-aux prf L |
          ι^Env-lemma-aux prf R = PEq.refl
ι^Env-lemma-aux prf  (`let M N)
  rewrite ι^Env-lemma-aux prf M |
          ι^Env-lemma-aux (ext₀^Env-ext₀ prf) N = PEq.refl

ι^Env-lemma : ∀ {f} {Γ} {σ} → (E : Exp {f} σ Γ) → (ι^Env *-Val E) ≡ E
ι^Env-lemma = ι^Env-lemma-aux {ρ = ι^Env} (λ v → PEq.refl)

ι^Env₀-lemma : ∀ {f} {σ} → (ρ : Env₀ ε) (E : Exp₀ {f} σ) → (ρ *-Val E) ≡ E
ι^Env₀-lemma ρ = ι^Env-lemma-aux {ρ = ρ} (λ ())

ι^Env₀ : ∀ {f} {σ} → (E : Exp₀ {f} σ) → (ι^Env {ε} *-Val E) ≡ E
ι^Env₀ = ι^Env-lemma {Γ = ε}

infixl 10 _⟨_/var₀⟩

_⟨_/var₀⟩ : ∀ {f} {σ τ} → [ σ ⊢ Exp {f} τ ⟶ Val σ ⟶ Exp {f} τ ]
E ⟨ U /var₀⟩ = subst E (ι^Env `∙ U)

-- composition of valuations: sub-sub fusion
_*-Sub_ : ∀ {Γ Δ Ξ} → (ρ : Δ ⊨ Ξ) → (ρ' : Γ ⊨ Δ) → Γ ⊨ Ξ
ρ *-Sub ρ' = map-Env (ρ *-Val_) ρ'
