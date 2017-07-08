{---------------------------------------------}
{-- Contexts and observational approximation -}
{---------------------------------------------}
module ivcc-apx where

open import Level as L using (Level ; _⊔_)
open import Data.Product hiding (map)
open import Data.List hiding (map ; [_])
open import Function as F hiding (_∋_ ; _$_)
open import Relation.Binary.PropositionalEquality as PEq using (_≡_)

open import lambda-fg
open import acmm
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

lemma35 : ∀ {f} {Γ} {σ τ} → (E : (σ ⊢ Exp {f} τ) Γ) → (ρ : Env₀ Γ) → ∀ U →
 subst E (ρ `∙ U) ≡ subst (E ⟨ Ren₀ *-Var U /var₀⟩) ρ
lemma35 E ρ U = lemma33 ρ (ι^Env `∙ (Ren₀ *-Var U)) E

subst-succ : ∀ {Γ} {σ τ} → (ρ : Env₀ (Γ ∙ τ)) → (M : Trm σ (Γ ∙ τ)) →
  subst (zero* ρ M) (succ ρ) ≡ subst M (succ ρ `∙ zero ρ)
-- subst-succ ρ M rewrite lemma35 M (succ ρ) (zero ρ) = PEq.refl 
subst-succ ρ M = PEq.sym (lemma33 (succ ρ) (ι^Env  `∙ (ren₀-zero ρ)) M)

-- iterated sequential substitution 'subst₀'

subst₀ : ∀ {Γ} {σ} → (ρ : Env₀ Γ) → (M : Trm σ Γ) → Trm₀ σ
subst₀ {ε} ρ M = M
subst₀ {Γ ∙ τ} ρ M = subst₀ (succ ρ) (zero* ρ M) 

-- parallel substitution 'subst' is iterated sequential substitution 'subst₀'

subst-equiv : ∀ {Γ} {σ} → (ρ : Env₀ Γ) → (M : Trm σ Γ) →
  subst₀ ρ M ≡ subst M ρ
subst-equiv   {ε}   ρ M rewrite ι^Env₀-lemma ρ M = PEq.refl
subst-equiv {Γ ∙ τ} ρ M rewrite subst-equiv (succ ρ) (zero* ρ M) | subst-succ ρ M
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

-- iterated βV redex construction

βVΓ : ∀ {Γ} {σ} → (ρ : Env₀ Γ) → (M : Trm σ Γ) → Trm₀ σ
βVΓ   {ε}   ρ M = M
βVΓ {Γ ∙ τ} ρ M = βVΓ (succ ρ) (βV M (ren₀-zero ρ))

βV-subst₀ : ∀ {Γ} {σ} → (ρ : Env₀ Γ) → (M : Trm σ Γ) → βVΓ ρ M →βV subst₀ ρ M
βV-subst₀   {ε}   ρ M = →βV-refl
βV-subst₀ {Γ ∙ τ} ρ M with βV-subst₀ (succ ρ) (βV M (ren₀-zero ρ))
... | ih 
      rewrite subst-equiv (succ ρ) (βV M (ren₀-zero ρ)) with →βV-step ih 
... | prf 
      rewrite subst-equiv (succ ρ) (zero* ρ M) | subst-succ ρ M | lemma34 M (succ ρ) (zero ρ) 
    = prf

-- variable-capturing contexts; no additional renaming/substitution in holes

infixr 20 IVCC⟪_⊢_⟫

data IVCC⟪_⊢_⟫ (Γ : Cx) (τ : Ty) : {f : CBV} → PreModel L.zero

 where

  `λ   : admits-λ λ {f} → IVCC⟪ Γ ⊢ τ ⟫ {f}

  `exp : ∀ {f} {σ} → [ Exp {f} σ ⟶ IVCC⟪ Γ ⊢ τ ⟫ {f} σ ]
    -- no holes; saves re-traversal

  ⟪-⟫  : IVCC⟪ Γ ⊢ τ ⟫ {`trm} τ Γ -- hole

  `val : {σ : Ty} → [ IVCC⟪ Γ ⊢ τ ⟫ {`val} σ  ⟶  IVCC⟪ Γ ⊢ τ ⟫ {`trm} σ ]
    -- lifting

  _`$_ : admits-$   λ {f} → IVCC⟪ Γ ⊢ τ ⟫ {f}
  `if  : admits-if  λ {f} → IVCC⟪ Γ ⊢ τ ⟫ {f}
  `let : admits-let λ {f} → IVCC⟪ Γ ⊢ τ ⟫ {f}

-- instantiation

_⟪_⟫IVCC : ∀ {f} {Γ Δ} {σ τ}
       (P : IVCC⟪ Γ ⊢ σ ⟫ {f} τ Δ) (T : Trm σ Γ) → Exp {f} τ Δ

`exp E ⟪ T ⟫IVCC =  E
`λ M   ⟪ T ⟫IVCC = `λ (M ⟪ T ⟫IVCC)

⟪-⟫    ⟪ T ⟫IVCC = T

(`val V)  ⟪ T ⟫IVCC = `val (V ⟪ T ⟫IVCC)

(V `$ W)  ⟪ T ⟫IVCC = (V ⟪ T ⟫IVCC) `$ (W ⟪ T ⟫IVCC)
`if B L R ⟪ T ⟫IVCC = `if  (B ⟪ T ⟫IVCC) (L ⟪ T ⟫IVCC) (R ⟪ T ⟫IVCC)
`let M N  ⟪ T ⟫IVCC = `let (M ⟪ T ⟫IVCC) (N ⟪ T ⟫IVCC)

-- action of substitution by iterated βV redex construction 

IVCC-sub : ∀ {Γ Δ} {σ τ} → Env₀ Δ → IVCC⟪ Γ ⊢ σ ⟫ {`trm} τ Δ →
  IVCC⟪ Γ ⊢ σ ⟫ {`trm} τ ε
IVCC-sub {Δ = ε} ρ C = C
IVCC-sub {Δ = Δ ∙ ω} ρ C =
  IVCC-sub (succ ρ) (`λ C `$ (`exp (ren₀-zero ρ))) 

-- commutes with instantiation 

IVCC-sub-βV : ∀ {Γ Δ} {σ τ} →
  (ρ : Env₀ Δ) → (C : IVCC⟪ Γ ⊢ σ ⟫ τ Δ) → (M : Trm σ Γ) → 
  (IVCC-sub ρ C) ⟪ M ⟫IVCC ≡ βVΓ ρ (C ⟪ M ⟫IVCC)
IVCC-sub-βV {Δ = ε}     ρ C M = PEq.refl
IVCC-sub-βV {Δ = Δ ∙ τ} ρ C =
  IVCC-sub-βV (succ ρ) ((`λ C) `$ (`exp (ren₀-zero ρ))) 

-- Observational simulation wrt IVCCs

ivcc-sim : ∀ {f} {Γ} {υ} → Rel^E {f} {L.zero} {Γ} {υ}
ivcc-sim {f} = case f return (λ f → ∀ {Γ} {υ} → Rel^E {f} {_} {Γ} {υ})
 of λ { `val → simV ; `trm → simT }
 where
  simV : ∀ {Γ} {τ} → Rel^V {_} {Γ} {τ}
  simT : ∀ {Γ} {τ} → Rel^T {_} {Γ} {τ}
  simV {Γ} {τ}     = _[ simT {Γ} {τ} ]^V_
  simT {Γ} {τ} M N =
    {υ : Ty} (P : IVCC⟪ Γ ⊢ τ ⟫ υ ε) → sim₀ {`trm} (P ⟪ M ⟫IVCC) (P ⟪ N ⟫IVCC)

-- open simulation follows trivially: use the obvious context, 
-- the substitution instance of the hole itself!

ivcc-sim→sim^T : ∀ {Γ} {τ} {M N} → ivcc-sim M N → sim {`trm} {Γ} {τ} M N
ivcc-sim→sim^T {Γ} {τ} {M} {N} sMN ρ = sim-subst
  where P : IVCC⟪ Γ ⊢ τ ⟫ τ ε
        P = IVCC-sub ρ ⟪-⟫ 

        βV-subst : ∀ M → (P ⟪ M ⟫IVCC) →βV subst M ρ
        βV-subst M rewrite IVCC-sub-βV ρ ⟪-⟫ M with βV-subst₀ ρ M 
        ... | prf rewrite subst-equiv ρ M = prf 

        sim-subst : sim₀ {`trm} (subst M ρ) (subst N ρ)
        sim-subst = lemma-2-10i-βV (βV-subst M) (lemma-2-10ii-βV (sMN P) (βV-subst N))
