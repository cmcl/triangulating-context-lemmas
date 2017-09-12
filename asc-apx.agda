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

-- Contexts; contextual equivalence; the intricate stuff
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

-- Applicative Substituting Contexts simulation/approximation
-- The fundamental relations, quantifying over all applicative contexts.

asc-sim : ∀ {f} {Γ} {υ} → Rel^E {f} {L.zero} {Γ} {υ}
asc-sim {f} = case f return (λ f → ∀ {Γ} {υ} → Rel^E {f} {_} {Γ} {υ})
 of λ { `val → simV ; `trm → simT }
 where
  simV : ∀ {Γ} {τ} → Rel^V {_} {Γ} {τ}
  simT : ∀ {Γ} {τ} → Rel^T {_} {Γ} {τ}
  simV {Γ} {τ}     = _[ simT {Γ} {τ} ]^V_
  simT {Γ} {τ} M N =
    {σ : Ty} (P : ASC⟪ Γ ⊢ τ ⟫ σ ε) → sim₀ {`trm} (P ⟪ M ⟫ASC) (P ⟪ N ⟫ASC)

-- open simulation follows trivially: use the obvious context, the hole
-- itself!

asc-sim→sim^T : ∀ {Γ} {τ} {M N} → asc-sim M N → sim {`trm} {Γ} {τ} M N
asc-sim→sim^T {Γ} {τ} sMN ρ = sMN P where P = ⟪- ρ -⟫

asc-sim₀ : GRel₀^E
asc-sim₀ {f} = case f return (λ f → ∀ {υ} → Rel^E {f} {_} {ε} {υ})
 of λ { `val → simV ; `trm → simT }
 where
  simV : GRel₀^V
  simT : GRel₀^T
  simV {τ} = _[ simT {τ} ]^V_
  simT     = asc-sim {`trm} {ε}

appVCC : ∀ {Γ Δ} {ω σ τ} →
  VCC⟪ Γ ⊢ ω ⟫ {`trm} (σ `→ τ) Δ → Val σ Δ → VCC⟪ Γ ⊢ ω ⟫ {`trm} τ Δ
appVCC P V = `let P (`exp (Val→Spine V))

asc-to-vcc : ∀ {Γ} {σ τ} → ASC⟪ Γ ⊢ σ ⟫ τ ε → VCC⟪ Γ ⊢ σ ⟫ {`trm} τ ε
asc-to-vcc ⟪- ρ -⟫ = VCC-sub ⟪- refl^Var -⟫ ρ
asc-to-vcc (P `* V) = appVCC (asc-to-vcc P) V

-- Reduction under application (term application simulated with let).
data _→$_ : GRel₀^T where
 →βV-$ : {σ : Ty} {M N : Trm₀ σ} → M →βV N → M →$ N
 →MN-$ : {σ τ : Ty} {M M' : Trm₀ σ} {N : (σ ⊢ Trm τ) _} →
   M →$ M' → `let M N →$ `let M' N

lemma-2-3i-$ : {τ : Ty} {M N : Trm₀ τ} {V : Val₀ τ} →
                (dev : M ⇓ V) → (red : M →$ N) → N ⇓ V
lemma-2-3i-$ dev (→βV-$ βV) = lemma-2-3i-βV dev βV
lemma-2-3i-$ (⇓let derM derN) (→MN-$ red) with lemma-2-3i-$ derM red
... | iH = ⇓let iH derN

lemma-2-3ii-$ : {τ : Ty} {M N : Trm₀ τ} {V : Val₀ τ} →
                 (red : M →$ N) → (dev : N ⇓ V) → M ⇓ V
lemma-2-3ii-$ (→βV-$ βV) dev = lemma-2-3ii-βV βV dev
lemma-2-3ii-$ (→MN-$ red) (⇓let derM derN) =
  ⇓let (lemma-2-3ii-$ red derM) derN

lemma-2-10i-$ : {ℓ^V : Level} {τ : Ty} {R : GRel^V {ℓ^V} {τ}}
  {M N P : Trm₀ τ} → M →$ P → (M [ R ]^T N) → P [ R ]^T N
lemma-2-10i-$ red r = r ∘ (lemma-2-3ii-$ red)

lemma-2-10ii-$ : {ℓ^V : Level} {τ : Ty} {R : GRel^V {ℓ^V} {τ}}
  {M N P : Trm₀ τ} → (M [ R ]^T N) → N →$ P → M [ R ]^T P
lemma-2-10ii-$ r red der with r der
... | V , derM , rUV = V , lemma-2-3i-$ derM red , rUV

→$-asc-vcc : ∀ {Γ} {σ τ} → (P : ASC⟪ Γ ⊢ σ ⟫ τ ε) → (M : Trm σ Γ) →
  ((asc-to-vcc P) ⟪ M ⟫VCC) →$ (P ⟪ M ⟫ASC)
→$-asc-vcc ⟪- ρ -⟫ M
  rewrite VCC-betaV ρ M ⟪- refl^Var -⟫ | ι^Var-lemma M = →βV-$ (betaV-Trm ρ M)
→$-asc-vcc (P `* V) M with →$-asc-vcc P M
... | →$PM = →MN-$ →$PM

vcc-sim→asc-sim^T : ∀ {Γ} {τ} {M N} →
  vcc-sim M N → asc-sim {`trm} {Γ} {τ} M N
vcc-sim→asc-sim^T {Γ} {τ} {M} {N} sMN ⟪- ρ -⟫ = vcc-sim→sim^T sMN ρ
vcc-sim→asc-sim^T {Γ} {τ} {M} {N} sMN (P `* V)
  with sMN (appVCC (asc-to-vcc P) V)
... | hyp = lemma-2-10i-$ (→MN-$ (→$-asc-vcc P M))
                          (lemma-2-10ii-$ hyp (→MN-$ (→$-asc-vcc P N)))

-- ASCs are contained within VSCs

cxt-sim→asc-sim^T : ∀ {Γ} {τ} {M N} → cxt-sim M N → asc-sim {`trm} {Γ} {τ} M N
cxt-sim→asc-sim^T {Γ} {τ} {M} {N} sMN with cxt-sim→vcc-sim^T sMN
... | sMN-VCC = vcc-sim→asc-sim^T sMN-VCC
