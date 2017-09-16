{---------------------------------------------}
{-- Contexts and observational approximation -}
{---------------------------------------------}
module vcc-apx where

open import Level as L using (Level ; _⊔_)
open import Data.Product hiding (map)
open import Data.List hiding (map ; [_])
open import Function as F hiding (_∋_ ; _$_)
open import Relation.Binary.PropositionalEquality as PEq using (_≡_)

open import lambda-fg
open import acmm
open import sim-fusion-lemmas
open import obs-apx
open import relations
open import big-step-prop

-- the null weakening/renaming 

Ren₀ : ∀ {Γ} → ε ⊆ Γ
var Ren₀ ()

-- generalities on non-empty (ground) substitutions

succ : ∀ {Γ Δ} {τ} → Γ ∙ τ ⊨ Δ → Γ ⊨ Δ
var (succ ρ) v = var ρ (su v)

zero : ∀ {Γ Δ} {τ} → Γ ∙ τ ⊨ Δ → Val τ Δ
zero ρ = var ρ ze

cons-rho : ∀ {Γ Δ} {σ} (ρ : Γ ∙ σ ⊨ Δ) →
 ∀ {τ} v → var (succ ρ `∙ zero ρ) v ≡ var ρ {τ} v 
cons-rho ρ ze = PEq.refl
cons-rho ρ (su v) = PEq.refl

ren₀-zero : ∀ {Γ} {τ} → Env₀ (Γ ∙ τ) → Val τ Γ 
ren₀-zero ρ = Ren₀ *-Var zero ρ 

zero* : ∀ {Γ} {σ τ} → Env₀ (Γ ∙ τ) → Trm σ (Γ ∙ τ) → Trm σ Γ 
zero* ρ M =  M ⟨ ren₀-zero ρ /var₀⟩ 

subst-succ : ∀ {Γ} {σ τ} → (ρ : Env₀ (Γ ∙ τ)) → (M : Trm σ (Γ ∙ τ)) →
  subst (zero* ρ M) (succ ρ) ≡ subst M (succ ρ `∙ zero ρ)
subst-succ ρ M = PEq.sym (lemma33 (succ ρ) (ι^Env  `∙ (ren₀-zero ρ)) M)

-- iterated sequential substitution 'subst₀'

subst₀ : ∀ {Γ} {σ} → (ρ : Env₀ Γ) → (M : Trm σ Γ) → Trm₀ σ
subst₀ {ε} ρ M = M
subst₀ {Γ ∙ τ} ρ M = subst₀ (succ ρ) (zero* ρ M) 

-- parallel substitution 'subst' is iterated sequential substitution 'subst₀'

subst-equiv : ∀ {Γ} {σ} → (ρ : Env₀ Γ) → (M : Trm σ Γ) →
  subst₀ ρ M ≡ subst M ρ
subst-equiv   {ε}   ρ M rewrite ι^Env₀-lemma ρ M = PEq.refl
subst-equiv {Γ ∙ τ} ρ M rewrite subst-equiv (succ ρ) (zero* ρ M) |
                                subst-succ ρ M
    = subst-ext M (cons-rho ρ)

-- iterated βV reduction

data _→βV_ : GRel₀^T where
  →βV-refl : {σ : Ty} {M : Trm₀ σ} → M →βV M
  →βV-step : {σ τ : Ty} {M : Trm₀ τ} {N : (σ ⊢ Trm τ) _} {V : _} →
    M →βV (βV N V) → M →βV (N ⟨ V /var₀⟩)

lemma-2-3i-βV : {τ : Ty} {M N : Trm₀ τ} {V : Val₀ τ} →
                (dev : M ⇓ V) → (red : M →βV N) → N ⇓ V
lemma-2-3i-βV dev →βV-refl = dev
lemma-2-3i-βV dev (→βV-step red) with lemma-2-3i-βV dev red
lemma-2-3i-βV dev (→βV-step red) | ⇓app der = der

lemma-2-3ii-βV : {τ : Ty} {M N : Trm₀ τ} {V : Val₀ τ} →
                 (red : M →βV N) → (dev : N ⇓ V) → M ⇓ V
lemma-2-3ii-βV →βV-refl dev = dev
lemma-2-3ii-βV (→βV-step red) dev = lemma-2-3ii-βV red (⇓app dev)

lemma-2-10i-βV : {ℓ^V : Level} {τ : Ty} {R : GRel^V {ℓ^V} {τ}}
  {M N P : Trm₀ τ} → M →βV P → (M [ R ]^T N) → P [ R ]^T N
lemma-2-10i-βV red r = r ∘ (lemma-2-3ii-βV red)

lemma-2-10ii-βV : {ℓ^V : Level} {τ : Ty} {R : GRel^V {ℓ^V} {τ}}
  {M N P : Trm₀ τ} → (M [ R ]^T N) → N →βV P → M [ R ]^T P
lemma-2-10ii-βV r red der with r der
... | V , derM , rUV = V , lemma-2-3i-βV derM red , rUV

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

-- iterated βV redex construction

βVΓ : ∀ {Γ} {σ} → (ρ : Env₀ Γ) → (M : Trm σ Γ) → Trm₀ σ
βVΓ   {ε}   ρ M = M
βVΓ {Γ ∙ τ} ρ M = βVΓ (succ ρ) (βV M (ren₀-zero ρ))

βV-subst₀ : ∀ {Γ} {σ} → (ρ : Env₀ Γ) → (M : Trm σ Γ) → βVΓ ρ M →βV subst M ρ
βV-subst₀   {ε}   ρ M rewrite ι^Env₀-lemma ρ M = →βV-refl
βV-subst₀ {Γ ∙ τ} ρ M with βV-subst₀ (succ ρ) (βV M (ren₀-zero ρ))
... | ih rewrite PEq.sym (subst-equiv ρ M) with →βV-step ih
... | prf rewrite subst-equiv (succ ρ) (zero* ρ M) | subst-succ ρ M |
                  lemma34 M (succ ρ) (zero ρ) = prf

-- variable-capturing contexts; no additional renaming/substitution in holes

infixr 20 VCC⟪_⊢_⟫

data VCC⟪_⊢_⟫ (Γ : Cx) (τ : Ty) : {f : CBV} → PreModel L.zero

 where

  `λ   : admits-λ λ {f} → VCC⟪ Γ ⊢ τ ⟫ {f}

  `exp : ∀ {f} {σ} → [ Exp {f} σ ⟶ VCC⟪ Γ ⊢ τ ⟫ {f} σ ]
    -- no holes; saves re-traversal

  ⟪-⟫  : VCC⟪ Γ ⊢ τ ⟫ {`trm} τ Γ -- hole

  `val : {σ : Ty} → [ VCC⟪ Γ ⊢ τ ⟫ {`val} σ  ⟶  VCC⟪ Γ ⊢ τ ⟫ {`trm} σ ]
    -- lifting

  _`$_ : admits-$   λ {f} → VCC⟪ Γ ⊢ τ ⟫ {f}
  `if  : admits-if  λ {f} → VCC⟪ Γ ⊢ τ ⟫ {f}
  `let : admits-let λ {f} → VCC⟪ Γ ⊢ τ ⟫ {f}

-- instantiation

_⟪_⟫VCC : ∀ {f} {Γ Δ} {σ τ}
       (P : VCC⟪ Γ ⊢ σ ⟫ {f} τ Δ) (T : Trm σ Γ) → Exp {f} τ Δ

`exp E ⟪ T ⟫VCC =  E
`λ M   ⟪ T ⟫VCC = `λ (M ⟪ T ⟫VCC)

⟪-⟫    ⟪ T ⟫VCC = T

(`val V)  ⟪ T ⟫VCC = `val (V ⟪ T ⟫VCC)

(V `$ W)  ⟪ T ⟫VCC = (V ⟪ T ⟫VCC) `$ (W ⟪ T ⟫VCC)
`if B L R ⟪ T ⟫VCC = `if  (B ⟪ T ⟫VCC) (L ⟪ T ⟫VCC) (R ⟪ T ⟫VCC)
`let M N  ⟪ T ⟫VCC = `let (M ⟪ T ⟫VCC) (N ⟪ T ⟫VCC)

-- action of substitution by iterated βV redex construction 

VCC-sub : ∀ {Γ Δ} {σ τ} → Env₀ Δ → VCC⟪ Γ ⊢ σ ⟫ {`trm} τ Δ →
  VCC⟪ Γ ⊢ σ ⟫ {`trm} τ ε
VCC-sub {Δ = ε} ρ C = C
VCC-sub {Δ = Δ ∙ ω} ρ C =
  VCC-sub (succ ρ) (`λ C `$ (`exp (ren₀-zero ρ))) 

-- commutes with instantiation 

VCC-sub-βV : ∀ {Γ Δ} {σ τ} →
  (ρ : Env₀ Δ) → (C : VCC⟪ Γ ⊢ σ ⟫ τ Δ) → (M : Trm σ Γ) → 
  (VCC-sub ρ C) ⟪ M ⟫VCC ≡ βVΓ ρ (C ⟪ M ⟫VCC)
VCC-sub-βV {Δ = ε}     ρ C M = PEq.refl
VCC-sub-βV {Δ = Δ ∙ τ} ρ C =
  VCC-sub-βV (succ ρ) ((`λ C) `$ (`exp (ren₀-zero ρ))) 

-- composition of contexts

_⟪∘⟫VCC_ : ∀ {f} {Γ Δ Ξ} {σ τ υ}
          (P : VCC⟪ Δ ⊢ σ ⟫ {f} τ Ξ)
          (Q : VCC⟪ Γ ⊢ υ ⟫ {`trm} σ Δ) → VCC⟪ Γ ⊢ υ ⟫ {f} τ Ξ
`exp E     ⟪∘⟫VCC Q = `exp E
`λ M       ⟪∘⟫VCC Q = `λ (M ⟪∘⟫VCC Q)
⟪-⟫        ⟪∘⟫VCC Q =  Q
`val P     ⟪∘⟫VCC Q = `val (P ⟪∘⟫VCC Q)
(F `$ A)   ⟪∘⟫VCC Q = F ⟪∘⟫VCC Q `$ A ⟪∘⟫VCC Q
`if B L R  ⟪∘⟫VCC Q = `if (B ⟪∘⟫VCC Q) (L ⟪∘⟫VCC Q) (R ⟪∘⟫VCC Q)
`let P R   ⟪∘⟫VCC Q = `let (P ⟪∘⟫VCC Q) (R ⟪∘⟫VCC Q)

-- commutation between composition and instantiation

_⟪∘_⟫VCC_ : ∀ {f} {Γ Δ Ξ} {σ τ υ} (P : VCC⟪ Δ ⊢ σ ⟫ {f} τ Ξ) (T : Trm υ Γ) →
       (Q : VCC⟪ Γ ⊢ υ ⟫ {`trm} σ Δ) →
       (P ⟪∘⟫VCC Q) ⟪ T ⟫VCC ≡ P ⟪ Q ⟪ T ⟫VCC ⟫VCC

`exp E    ⟪∘ T ⟫VCC Q = PEq.refl
`λ M      ⟪∘ T ⟫VCC Q rewrite M ⟪∘ T ⟫VCC Q = PEq.refl

⟪-⟫       ⟪∘ T ⟫VCC Q = PEq.refl
`val P    ⟪∘ T ⟫VCC Q rewrite P ⟪∘ T ⟫VCC Q = PEq.refl
(F `$ A)  ⟪∘ T ⟫VCC Q rewrite F ⟪∘ T ⟫VCC Q | A ⟪∘ T ⟫VCC Q = PEq.refl
`if B L R ⟪∘ T ⟫VCC Q
  rewrite B ⟪∘ T ⟫VCC Q | L ⟪∘ T ⟫VCC Q | R ⟪∘ T ⟫VCC Q = PEq.refl
`let P R  ⟪∘ T ⟫VCC Q rewrite P ⟪∘ T ⟫VCC Q | R ⟪∘ T ⟫VCC Q = PEq.refl

-- commutation between substitution and instantiation

-- _substVCC⟪_⟫_ : ∀ {f} {τ υ} {Γ Δ Ξ}
--                 (P : VCC⟪ Γ ⊢ τ ⟫ {f} υ ε) (T : Trm τ Γ) (ρ : Env₀ Γ) →
--  subst (Ren₀ *-Var P ⟪ T ⟫VCC) ρ ≡ P ⟪ subst T ρ ⟫VCC
-- P substVCC⟪ T ⟫ ρ = ?

-- Observational simulation wrt VCCs

vcc-sim : ∀ {f} {Γ} {υ} → Rel^E {f} {L.zero} {Γ} {υ}
vcc-sim {f} = case f return (λ f → ∀ {Γ} {υ} → Rel^E {f} {_} {Γ} {υ})
 of λ { `val → simV ; `trm → simT }
 where
  simV : ∀ {Γ} {τ} → Rel^V {_} {Γ} {τ}
  simT : ∀ {Γ} {τ} → Rel^T {_} {Γ} {τ}
  simV {Γ} {τ}     = _[ simT {Γ} {τ} ]^V_
  simT {Γ} {τ} M N =
    {υ : Ty} (P : VCC⟪ Γ ⊢ τ ⟫ υ ε) → sim₀ {`trm} (P ⟪ M ⟫VCC) (P ⟪ N ⟫VCC)

-- open simulation follows trivially: use the obvious context, 
-- the substitution instance of the hole itself!

vcc-sim→sim^T : ∀ {Γ} {τ} {M N} → vcc-sim M N → sim {`trm} {Γ} {τ} M N
vcc-sim→sim^T {Γ} {τ} {M} {N} sMN ρ = sim-subst
  where P : VCC⟪ Γ ⊢ τ ⟫ τ ε
        P = VCC-sub ρ ⟪-⟫ 

        βV-subst : ∀ M → (P ⟪ M ⟫VCC) →βV subst M ρ
        βV-subst M rewrite VCC-sub-βV ρ ⟪-⟫ M with βV-subst₀ ρ M 
        ... | prf rewrite subst-equiv ρ M = prf 

        sim-subst : sim₀ {`trm} (subst M ρ) (subst N ρ)
        sim-subst = lemma-2-10i-βV (βV-subst M)
                                   (lemma-2-10ii-βV (sMN P) (βV-subst N))

vcc-sim₀ : GRel₀^E
vcc-sim₀ {f} = case f return (λ f → ∀ {υ} → Rel^E {f} {_} {ε} {υ})
 of λ { `val → simV ; `trm → simT }
 where
  simV : GRel₀^V
  simT : GRel₀^T
  simV {τ} = _[ simT {τ} ]^V_
  simT     = vcc-sim {`trm} {ε}

-- Convert an VCC to a VSC

vcc-to-cxt : ∀ {f} {Γ Δ} {σ τ} → VCC⟪ Γ ⊢ σ ⟫ {f} τ Δ → Cxt⟪ Γ ⊢ σ ⟫ {f} τ Δ
vcc-to-cxt (`λ M) = `λ (vcc-to-cxt M)
vcc-to-cxt (`exp E) = `exp E
vcc-to-cxt ⟪-⟫ = ⟪- ι^Env -⟫
vcc-to-cxt (`val P) = `val (vcc-to-cxt P)
vcc-to-cxt (F `$ A) = (vcc-to-cxt F) `$ (vcc-to-cxt A)
vcc-to-cxt (`if B L R) = `if (vcc-to-cxt B) (vcc-to-cxt L) (vcc-to-cxt R)
vcc-to-cxt (`let P Q) = `let (vcc-to-cxt P) (vcc-to-cxt Q)

vcc→cxt⟪_⟫ : ∀ {f} {Γ Δ} {σ τ} →
  (M : Trm σ Γ) → (P : VCC⟪ Γ ⊢ σ ⟫ {f} τ Δ) →
  (vcc-to-cxt P) ⟪ M ⟫ ≡ P ⟪ M ⟫VCC
vcc→cxt⟪ M ⟫ (`λ P) rewrite vcc→cxt⟪ M ⟫ P = PEq.refl
vcc→cxt⟪ M ⟫ (`exp E) = PEq.refl
vcc→cxt⟪ M ⟫ ⟪-⟫ = ι^Env-lemma M
vcc→cxt⟪ M ⟫ (`val P) rewrite vcc→cxt⟪ M ⟫ P = PEq.refl
vcc→cxt⟪ M ⟫ (F `$ A) rewrite vcc→cxt⟪ M ⟫ F | vcc→cxt⟪ M ⟫ A = PEq.refl
vcc→cxt⟪ M ⟫ (`if B L R)
  rewrite vcc→cxt⟪ M ⟫ B | vcc→cxt⟪ M ⟫ L | vcc→cxt⟪ M ⟫ R = PEq.refl
vcc→cxt⟪ M ⟫ (`let P Q) rewrite vcc→cxt⟪ M ⟫ P | vcc→cxt⟪ M ⟫ Q = PEq.refl

-- VCCs are contained within VSCs

cxt-sim→vcc-sim^T :
  ∀ {Γ} {τ} {M N} → cxt-sim M N → vcc-sim {`trm} {Γ} {τ} M N
cxt-sim→vcc-sim^T {Γ} {τ} {M} {N} sMN P with sMN (vcc-to-cxt P)
... | hyp rewrite vcc→cxt⟪ M ⟫ P | vcc→cxt⟪ N ⟫ P = hyp

cxt-sim₀→vcc-sim₀^T : ∀ {τ} {M N : Trm₀ τ} → cxt-sim₀ M N → vcc-sim₀ M N
cxt-sim₀→vcc-sim₀^T = cxt-sim→vcc-sim^T {ε}
