{----------------------------------------------------}
{-- Applicative Substituting Contexts approximation -}
{----------------------------------------------------}
module asc-apx where

open import Level as L using (Level ; _⊔_)
open import Data.Product hiding (map)
open import Function as F hiding (_∋_ ; _$_)
open import Relation.Binary.PropositionalEquality as PEq using (_≡_)

open import lambda-fg
open import acmm
open import relations
open import sim-fusion-lemmas
open import obs-apx
open import vcc-apx
open import big-step-prop

infixr 20 ⟪-_-⟫
infixr 20 _⟪_⟫ASC
infixr 20 _⟪∘⟫ASC_
infixr 20 _⟪∘_⟫ASC_
infixr 20 ASC⟪_⊢_⟫

infixl 5 _`*_

data ASC⟪_⊢_⟫ (Γ : Cx) (τ : Ty) : PreModel L.zero

 where
  ⟪-_-⟫ : [ Γ ⊨_  ⟶  ASC⟪ Γ ⊢ τ ⟫ τ ]
    -- {Δ : Cx} → (ρ : Γ ⊨ Δ) → ASC {Γ} {σ} σ Δ

  _`*_ : ∀ {σ ω} → [ ASC⟪ Γ ⊢ τ ⟫ (σ `→ ω) ⟶ Val σ ⟶ ASC⟪ Γ ⊢ τ ⟫ ω ]

_⟪_⟫ASC : ∀ {Γ Δ} {σ τ} (P : ASC⟪ Γ ⊢ σ ⟫ τ Δ) (T : Trm σ Γ) → Trm τ Δ
⟪- ρ -⟫ ⟪ T ⟫ASC = subst T ρ
(P `* V) ⟪ T ⟫ASC = appT (P ⟪ T ⟫ASC) V

-- a distinguished example: action of Val substitution on contexts

substASC : ∀ {τ υ} {Γ Δ Ξ}
         (P : ASC⟪ Γ ⊢ τ ⟫ υ Δ) → (ρ : Δ ⊨ Ξ) → ASC⟪ Γ ⊢ τ ⟫ υ Ξ

substASC ⟪- ρ' -⟫    ρ = ⟪- ρ *-Sub ρ' -⟫
substASC (F `* V)    ρ = (substASC F ρ) `* (subst V ρ)

-- commutation between substitution and instantiation

_substASC⟪_⟫_ : ∀ {τ υ} {Γ Δ Ξ}
                (C : ASC⟪ Γ ⊢ τ ⟫ υ Δ) (T : Trm τ Γ) (ρ : Δ ⊨ Ξ) →
 substASC C ρ ⟪ T ⟫ASC ≡ subst (C ⟪ T ⟫ASC) ρ
⟪- ρ' -⟫ substASC⟪ T ⟫ ρ rewrite lemma33 ρ ρ' T  = PEq.refl
(_`*_ {σ} {ω} F V) substASC⟪ T ⟫ ρ
  rewrite F substASC⟪ T ⟫ ρ |
          ren-sub→sub-ren V (weak {σ = σ `→ ω}) weak (ext₀^Env ρ) ρ
                          (λ v → PEq.refl)
  = PEq.refl

-- composition of contexts

_⟪∘⟫ASC_ : ∀ {Γ Δ Ξ} {σ τ υ}
          (P : ASC⟪ Δ ⊢ σ ⟫ τ Ξ)
          (Q : ASC⟪ Γ ⊢ υ ⟫ σ Δ) → ASC⟪ Γ ⊢ υ ⟫ τ Ξ
⟪- ρ -⟫  ⟪∘⟫ASC Q =  substASC Q ρ
(F `* V) ⟪∘⟫ASC Q = F ⟪∘⟫ASC Q `* V


-- commutation between composition and instantiation

_⟪∘_⟫ASC_ : ∀ {Γ Δ Ξ} {σ τ υ} (P : ASC⟪ Δ ⊢ σ ⟫ τ Ξ) (T : Trm υ Γ) →
           (Q : ASC⟪ Γ ⊢ υ ⟫ σ Δ) →
          (P ⟪∘⟫ASC Q) ⟪ T ⟫ASC ≡ P ⟪ Q ⟪ T ⟫ASC ⟫ASC
⟪- ρ -⟫   ⟪∘ T ⟫ASC Q = Q substASC⟪ T ⟫ ρ
(F `* V)  ⟪∘ T ⟫ASC Q rewrite F ⟪∘ T ⟫ASC Q = PEq.refl

-- Applicative Substituting Contexts approximation
-- The fundamental relations, quantifying over all applicative contexts.

asc-apx : ∀ {f} {Γ} {υ} → Rel^E {f} {L.zero} {Γ} {υ}
asc-apx {f} = case f return (λ f → ∀ {Γ} {υ} → Rel^E {f} {_} {Γ} {υ})
 of λ { `val → apxV ; `trm → apxT }
 where
  apxV : ∀ {Γ} {τ} → Rel^V {_} {Γ} {τ}
  apxT : ∀ {Γ} {τ} → Rel^T {_} {Γ} {τ}
  apxV {Γ} {τ}     = _[ apxT {Γ} {τ} ]^V_
  apxT {Γ} {τ} M N =
    {σ : Ty} (P : ASC⟪ Γ ⊢ τ ⟫ σ ε) →
    gnd-eqv₀ {`trm} (P ⟪ M ⟫ASC) (P ⟪ N ⟫ASC)

-- open ground equivalence follows trivially: use the obvious context, the hole
-- itself!

asc-apx→gnd-eqv^T : ∀ {Γ} {τ} {M N} → asc-apx M N → gnd-eqv {`trm} {Γ} {τ} M N
asc-apx→gnd-eqv^T {Γ} {τ} sMN ρ = sMN P where P = ⟪- ρ -⟫

asc-apx₀ : GRel₀^E
asc-apx₀ {f} = case f return (λ f → ∀ {υ} → Rel^E {f} {_} {ε} {υ})
 of λ { `val → apxV ; `trm → apxT }
 where
  apxV : GRel₀^V
  apxT : GRel₀^T
  apxV {τ} = _[ apxT {τ} ]^V_
  apxT     = asc-apx {`trm} {ε}

appVCC : ∀ {Γ Δ} {ω σ τ} →
  VCC⟪ Γ ⊢ ω ⟫ {`trm} (σ `→ τ) Δ → Val σ Δ → VCC⟪ Γ ⊢ ω ⟫ {`trm} τ Δ
appVCC P V = `let P (`exp (Val→Spine V))

asc-to-vcc : ∀ {Γ} {σ τ} → ASC⟪ Γ ⊢ σ ⟫ τ ε → VCC⟪ Γ ⊢ σ ⟫ {`trm} τ ε
asc-to-vcc ⟪- ρ -⟫ = VCC-sub ρ ⟪-⟫
asc-to-vcc (P `* V) = appVCC (asc-to-vcc P) V

→$-asc-vcc : ∀ {Γ} {σ τ} → (P : ASC⟪ Γ ⊢ σ ⟫ τ ε) → (M : Trm σ Γ) →
  ((asc-to-vcc P) ⟪ M ⟫VCC) →$ (P ⟪ M ⟫ASC)
→$-asc-vcc ⟪- ρ -⟫ M rewrite VCC-sub-βV ρ ⟪-⟫ M = →βV-$ (βV-subst₀ ρ M)
→$-asc-vcc (P `* V) M with →$-asc-vcc P M
... | →$PM = →MN-$ →$PM

vcc-apx→asc-apx^T : ∀ {Γ} {τ} {M N} →
  vcc-apx M N → asc-apx {`trm} {Γ} {τ} M N
vcc-apx→asc-apx^T {Γ} {τ} {M} {N} sMN ⟪- ρ -⟫ = vcc-apx→gnd-eqv^T sMN ρ
vcc-apx→asc-apx^T {Γ} {τ} {M} {N} sMN (P `* V)
  with sMN (asc-to-vcc (P `* V))
... | hyp = lemma-2-10i-$ (→MN-$ (→$-asc-vcc P M))
                          (lemma-2-10ii-$ hyp (→MN-$ (→$-asc-vcc P N)))

vcc-apx₀→asc-apx₀^T : ∀ {τ} {M N : Trm₀ τ} → vcc-apx₀ M N → asc-apx₀ M N
vcc-apx₀→asc-apx₀^T = vcc-apx→asc-apx^T {ε}

-- ASC apx is contained within VSC apx.

vsc-apx→asc-apx^T : ∀ {Γ} {τ} {M N} → vsc-apx M N → asc-apx {`trm} {Γ} {τ} M N
vsc-apx→asc-apx^T {Γ} {τ} {M} {N} sMN with vsc-apx→vcc-apx^T sMN
... | sMN-VCC = vcc-apx→asc-apx^T sMN-VCC
