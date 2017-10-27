{---------------------------------------------------------}
{-- Closed Instantiation of a Use Contexts approximation -}
{---------------------------------------------------------}
module ciu-apx where

open import Level as L using (Level ; _⊔_)
open import Function as F hiding (_∋_ ; _$_)
open import Relation.Binary.PropositionalEquality as PEq using (_≡_)

open import acmm
open import relations
open import sim-fusion-lemmas
open import obs-apx
open import vcc-apx
open import big-step-prop

-- CIU Contexts
infixr 20 ⟪-_-⟫
infixr 20 _⟪_⟫CIU
infixr 20 _⟪∘⟫CIU_
infixr 20 _⟪∘_⟫CIU_
infixr 20 CIU⟪_⊢_⟫

infixl 5 _`⋉_

data CIU⟪_⊢_⟫ (Γ : Cx) (τ : Ty) : PreModel L.zero

 where
  ⟪-_-⟫ : [ Γ ⊨_  ⟶  CIU⟪ Γ ⊢ τ ⟫ τ ]
    -- {Δ : Cx} → (ρ : Γ ⊨ Δ) → CIU {Γ} {σ} σ Δ

  _`⋉_ : ∀ {σ ω} → [ CIU⟪ Γ ⊢ τ ⟫ σ ⟶ σ ⊢ Trm ω ⟶ CIU⟪ Γ ⊢ τ ⟫ ω ]

_⟪_⟫CIU : ∀ {Γ Δ} {σ τ} (P : CIU⟪ Γ ⊢ σ ⟫ τ Δ) (T : Trm σ Γ) → Trm τ Δ
⟪- ρ -⟫ ⟪ T ⟫CIU = subst T ρ
(P `⋉ M) ⟪ T ⟫CIU = `let (P ⟪ T ⟫CIU) M

-- a distinguished example: action of Val substitution on contexts

substCIU : ∀ {τ υ} {Γ Δ Ξ}
         (P : CIU⟪ Γ ⊢ τ ⟫ υ Δ) → (ρ : Δ ⊨ Ξ) → CIU⟪ Γ ⊢ τ ⟫ υ Ξ

substCIU ⟪- ρ' -⟫    ρ = ⟪- ρ *-Sub ρ' -⟫
substCIU (P `⋉ M)    ρ = (substCIU P ρ) `⋉ (subst M (ext₀^Env ρ))


-- commutation between substitution and instantiation

_substCIU⟪_⟫_ : ∀ {τ υ} {Γ Δ Ξ}
                (C : CIU⟪ Γ ⊢ τ ⟫ υ Δ) (T : Trm τ Γ) (ρ : Δ ⊨ Ξ) →
 substCIU C ρ ⟪ T ⟫CIU ≡ subst (C ⟪ T ⟫CIU) ρ
⟪- ρ' -⟫ substCIU⟪ T ⟫ ρ rewrite lemma33 ρ ρ' T  = PEq.refl
(_`⋉_ {σ} {ω} P M) substCIU⟪ T ⟫ ρ rewrite P substCIU⟪ T ⟫ ρ = PEq.refl


-- composition of contexts

_⟪∘⟫CIU_ : ∀ {Γ Δ Ξ} {σ τ υ}
          (P : CIU⟪ Δ ⊢ σ ⟫ τ Ξ)
          (Q : CIU⟪ Γ ⊢ υ ⟫ σ Δ) → CIU⟪ Γ ⊢ υ ⟫ τ Ξ
⟪- ρ -⟫  ⟪∘⟫CIU Q =  substCIU Q ρ
(P `⋉ M) ⟪∘⟫CIU Q = P ⟪∘⟫CIU Q `⋉ M

-- commutation between composition and instantiation

_⟪∘_⟫CIU_ : ∀ {Γ Δ Ξ} {σ τ υ} (P : CIU⟪ Δ ⊢ σ ⟫ τ Ξ) (T : Trm υ Γ) →
           (Q : CIU⟪ Γ ⊢ υ ⟫ σ Δ) →
          (P ⟪∘⟫CIU Q) ⟪ T ⟫CIU ≡ P ⟪ Q ⟪ T ⟫CIU ⟫CIU
⟪- ρ -⟫   ⟪∘ T ⟫CIU Q = Q substCIU⟪ T ⟫ ρ
(F `⋉ V)  ⟪∘ T ⟫CIU Q rewrite F ⟪∘ T ⟫CIU Q = PEq.refl

-- CIU approximation
-- The fundamental relations, quantifying over all CIU contexts.

ciu-apx : ∀ {f} {Γ} {υ} → Rel^E {f} {L.zero} {Γ} {υ}
ciu-apx {f} = case f return (λ f → ∀ {Γ} {υ} → Rel^E {f} {_} {Γ} {υ})
 of λ { `val → apxV ; `trm → apxT }
 where
  apxV : ∀ {Γ} {τ} → Rel^V {_} {Γ} {τ}
  apxT : ∀ {Γ} {τ} → Rel^T {_} {Γ} {τ}
  apxV {Γ} {τ}     = _[ apxT {Γ} {τ} ]^V_
  apxT {Γ} {τ} M N =
    {σ : Ty} (P : CIU⟪ Γ ⊢ τ ⟫ σ ε) →
    gnd-eqv₀ {`trm} (P ⟪ M ⟫CIU) (P ⟪ N ⟫CIU)

-- open ground equivalence follows trivially: use the obvious context, the
-- hole itself!

ciu-apx→gnd-eqv^T : ∀ {Γ} {τ} {M N} → ciu-apx M N → gnd-eqv {`trm} {Γ} {τ} M N
ciu-apx→gnd-eqv^T {Γ} {τ} sMN ρ = sMN P where P = ⟪- ρ -⟫

ciu-apx₀ : GRel₀^E
ciu-apx₀ {f} = case f return (λ f → ∀ {υ} → Rel^E {f} {_} {ε} {υ})
 of λ { `val → apxV ; `trm → apxT }
 where
  apxV : GRel₀^V
  apxT : GRel₀^T
  apxV {τ} = _[ apxT {τ} ]^V_
  apxT     = ciu-apx {`trm} {ε}

-- The black diamond operator in the paper.
ciu-to-vcc : ∀ {Γ} {σ τ} → CIU⟪ Γ ⊢ σ ⟫ τ ε → VCC⟪ Γ ⊢ σ ⟫ {`trm} τ ε
ciu-to-vcc ⟪- ρ -⟫ = VCC-sub ρ ⟪-⟫
ciu-to-vcc (P `⋉ M) = `let (ciu-to-vcc P) (`exp M)

→$-ciu-vcc⟪_⟫ : ∀ {Γ} {σ τ} → (T : Trm σ Γ) → (P : CIU⟪ Γ ⊢ σ ⟫ τ ε) →
  ((ciu-to-vcc P) ⟪ T ⟫VCC) →$ (P ⟪ T ⟫CIU)
→$-ciu-vcc⟪ T ⟫ ⟪- ρ -⟫ rewrite VCC-sub-βV ρ ⟪-⟫ T = →βV-$ (βV-subst₀ ρ T)
→$-ciu-vcc⟪ T ⟫ (P `⋉ M) = →MN-$ (→$-ciu-vcc⟪ T ⟫ P)

vcc-apx→ciu-apx^T : ∀ {Γ} {τ} {M N} →
  vcc-apx M N → ciu-apx {`trm} {Γ} {τ} M N
vcc-apx→ciu-apx^T {Γ} {τ} {M} {N} sMN ⟪- ρ -⟫ = vcc-apx→gnd-eqv^T sMN ρ
vcc-apx→ciu-apx^T {Γ} {τ} {M} {N} sMN (P `⋉ T)
  with sMN (ciu-to-vcc (P `⋉ T))
... | hyp = lemma-2-10i-$ (→MN-$ (→$-ciu-vcc⟪ M ⟫ P))
                          (lemma-2-10ii-$ hyp (→MN-$ (→$-ciu-vcc⟪ N ⟫ P)))

-- CIU apx is contained within VSC apx.

vsc-apx→ciu-apx^T : ∀ {Γ} {τ} {M N} → vsc-apx M N → ciu-apx {`trm} {Γ} {τ} M N
vsc-apx→ciu-apx^T {Γ} {τ} {M} {N} sMN with vsc-apx→vcc-apx^T sMN
... | sMN-VCC = vcc-apx→ciu-apx^T sMN-VCC
