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
open import obs-apx
open import relations
open import big-step-prop

-- Contexts; contextual equivalence; the intricate stuff

infixr 20 ⟪-_-⟫
{-
infixr 20 _⟪_⟫
infixr 20 _⟪∘⟫_
infixr 20 _⟪∘_⟫_
-}
infixr 20 VCC⟪_⊢_⟫

data VCC⟪_⊢_⟫ (Γ : Cx) (τ : Ty) : {f : CBV} → PreModel L.zero

 where

  `λ   : admits-λ λ {f} → VCC⟪ Γ ⊢ τ ⟫ {f}

  `exp : ∀ {f} {σ} → [ Exp {f} σ ⟶ VCC⟪ Γ ⊢ τ ⟫ {f} σ ]
    -- no holes; saves re-traversal

  ⟪-_-⟫ : [ Γ ⊆_ ⟶ VCC⟪ Γ ⊢ τ ⟫ {`trm} τ ] -- hole

  `val : {σ : Ty} → [ VCC⟪ Γ ⊢ τ ⟫ {`val} σ  ⟶  VCC⟪ Γ ⊢ τ ⟫ {`trm} σ ]
    -- lifting

  _`$_ : admits-$   λ {f} → VCC⟪ Γ ⊢ τ ⟫ {f}
  `if  : admits-if  λ {f} → VCC⟪ Γ ⊢ τ ⟫ {f}
  `let : admits-let λ {f} → VCC⟪ Γ ⊢ τ ⟫ {f}

_⟪_⟫VCC : ∀ {f} {Γ Δ} {σ τ}
       (P : VCC⟪ Γ ⊢ σ ⟫ {f} τ Δ) (T : Trm σ Γ) → Exp {f} τ Δ

`exp E ⟪ T ⟫VCC =  E
`λ M   ⟪ T ⟫VCC = `λ (M ⟪ T ⟫VCC)

⟪- r -⟫   ⟪ T ⟫VCC = r *-Var T

(`val V)  ⟪ T ⟫VCC = `val (V ⟪ T ⟫VCC)

(V `$ W)  ⟪ T ⟫VCC = (V ⟪ T ⟫VCC) `$ (W ⟪ T ⟫VCC)
`if B L R ⟪ T ⟫VCC = `if  (B ⟪ T ⟫VCC) (L ⟪ T ⟫VCC) (R ⟪ T ⟫VCC)
`let M N  ⟪ T ⟫VCC = `let (M ⟪ T ⟫VCC) (N ⟪ T ⟫VCC)

Ren₀ : ∀ {Γ} → ε ⊆ Γ
Ren₀ {ε} = refl^Var
Ren₀ {Γ ∙ x} = trans^Var (Ren₀ {Γ}) weak

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

suc : ∀ {Γ Δ} {τ} → Γ ∙ τ ⊨ Δ → Γ ⊨ Δ
var (suc ρ) v = var ρ (su v)

zero : ∀ {Γ Δ} {τ} → Γ ∙ τ ⊨ Δ → Val τ Δ
zero ρ = var ρ ze

cons-rho : ∀ {Γ} {σ} (ρ : Env₀ (Γ ∙ σ)) →
 ∀ {τ} v → var ρ {τ} v ≡ var (suc ρ `∙ var ρ ze) v
cons-rho ρ ze = PEq.refl
cons-rho ρ (su v) = PEq.refl

subst-rho : ∀ {Γ} {σ} → (ρ : Env₀ Γ) → (M : Trm σ Γ) → Trm₀ σ
subst-rho {ε} ρ M = M
subst-rho {Γ ∙ τ} ρ M = subst-rho (suc ρ) (M ⟨ Ren₀ *-Var var ρ ze /var₀⟩)

lemma35 : ∀ {f} {Γ} {σ τ} → (E : (σ ⊢ Exp {f} τ) Γ) → (ρ : Γ ⊨ ε) → ∀ U →
 subst E (ρ `∙ U) ≡ subst (E ⟨ Ren₀ *-Var U /var₀⟩) ρ
lemma35 E ρ U = lemma33 ρ (ι^Env `∙ (Ren₀ *-Var U)) E

subst-suc : ∀ {Γ} {σ τ} → (ρ : Γ ∙ τ ⊨ ε) → (M : Trm σ (Γ ∙ τ)) →
  subst (M ⟨ Ren₀ *-Var zero ρ /var₀⟩) (suc ρ) ≡ subst M (suc ρ `∙ zero ρ)
subst-suc ρ M rewrite lemma35 M (suc ρ) (zero ρ) = PEq.refl

subst-equiv : ∀ {Γ} {σ} → (ρ : Env₀ Γ) → (M : Trm σ Γ) →
  subst-rho ρ M ≡ subst M ρ
subst-equiv {ε} ρ M rewrite ι^Env₀-lemma ρ M = PEq.refl
subst-equiv {Γ ∙ τ} ρ M
  rewrite subst-equiv (suc ρ) (M ⟨ Ren₀ *-Var zero ρ /var₀⟩) | subst-suc ρ M
  = subst-ext M (cons-rho ρ)

βVΓ : ∀ {Γ} {σ} → (ρ : Γ ⊨ ε) → (M : Trm σ Γ) → Trm₀ σ
βVΓ {ε} ρ M = M
βVΓ {Γ ∙ τ} ρ M = βVΓ (suc ρ) ((`λ M) `$ (Ren₀ *-Var zero ρ))

data _→βV_ : GRel₀^T where
  →βV-refl : {σ : Ty} {M : Trm₀ σ} → M →βV M
  →βV-step : {σ τ : Ty} {M : Trm₀ τ} {N : (σ ⊢ Trm τ) _} {V : _} →
    M →βV (`λ N `$ V) → M →βV (N ⟨ V /var₀⟩)

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

betaV-Trm : ∀ {Γ} {σ} → (ρ : Γ ⊨ ε) → (M : Trm σ Γ) → βVΓ ρ M →βV subst M ρ
betaV-Trm   {ε}   ρ M rewrite PEq.sym (subst-equiv ρ M) = →βV-refl
betaV-Trm {Γ ∙ τ} ρ M with betaV-Trm (suc ρ) (βV M (Ren₀ *-Var zero ρ))
... | ih rewrite PEq.sym (subst-equiv ρ M) |
                 subst-equiv (suc ρ) (M ⟨ Ren₀ *-Var zero ρ /var₀⟩) |
                 subst-suc ρ M | lemma34 M (suc ρ) (zero ρ) = →βV-step ih

VCC-sub : ∀ {Γ Δ} {σ τ} → VCC⟪ Γ ⊢ σ ⟫ {`trm} τ Δ → Δ ⊨ ε →
  VCC⟪ Γ ⊢ σ ⟫ {`trm} τ ε
VCC-sub {Δ = ε} cxt ρ = cxt
VCC-sub {Δ = Δ ∙ ω} cxt ρ =
  VCC-sub (`λ cxt `$ (`exp (Ren₀ *-Var (var ρ ze)))) (suc ρ)

VCC-betaV : ∀ {Γ Δ} {σ τ} →
  (ρ : Δ ⊨ ε) → (M : Trm σ Γ) → (C : VCC⟪ Γ ⊢ σ ⟫ τ Δ) →
  (VCC-sub C ρ) ⟪ M ⟫VCC ≡ βVΓ ρ (C ⟪ M ⟫VCC)
VCC-betaV {Δ = ε} ρ M C = PEq.refl
VCC-betaV {Δ = Δ ∙ τ}  ρ M C =
  VCC-betaV (suc ρ) M ((`λ C) `$ (`exp (Ren₀ *-Var (zero ρ))))

-- Ground simulation
-- The most boring relation of them all, but which ensures termination.
-- Moreover, it's an equivalence relation!
vcc-sim : ∀ {f} {Γ} {υ} → Rel^E {f} {L.zero} {Γ} {υ}
vcc-sim {f} = case f return (λ f → ∀ {Γ} {υ} → Rel^E {f} {_} {Γ} {υ})
 of λ { `val → simV ; `trm → simT }
 where
  simV : ∀ {Γ} {τ} → Rel^V {_} {Γ} {τ}
  simT : ∀ {Γ} {τ} → Rel^T {_} {Γ} {τ}
  simV {Γ} {τ}     = _[ simT {Γ} {τ} ]^V_
  simT {Γ} {τ} M N =
    {υ : Ty} (P : VCC⟪ Γ ⊢ τ ⟫ υ ε) → sim₀ {`trm} (P ⟪ M ⟫VCC) (P ⟪ N ⟫VCC)

-- open simulation follows trivially: use the obvious context, the hole
-- itself!

vcc-sim→sim^T : ∀ {Γ} {τ} {M N} → vcc-sim M N → sim {`trm} {Γ} {τ} M N
vcc-sim→sim^T {Γ} {τ} {M} {N} sMN ρ = sim-subst
  where P : VCC⟪ Γ ⊢ τ ⟫ τ ε
        P = VCC-sub ⟪- refl^Var -⟫ ρ

        βV-M : (P ⟪ M ⟫VCC) →βV subst M ρ
        βV-M rewrite VCC-betaV ρ M ⟪- refl^Var -⟫ | ι^Var-lemma M =
          betaV-Trm ρ M

        βV-N : (P ⟪ N ⟫VCC) →βV subst N ρ
        βV-N rewrite VCC-betaV ρ N ⟪- refl^Var -⟫ | ι^Var-lemma N =
          betaV-Trm ρ N

        sim-subst : sim₀ {`trm} (subst M ρ) (subst N ρ)
        sim-subst = lemma-2-10i-βV βV-M (lemma-2-10ii-βV (sMN P) βV-N)

vcc-sim₀ : GRel₀^E
vcc-sim₀ {f} = case f return (λ f → ∀ {υ} → Rel^E {f} {_} {ε} {υ})
 of λ { `val → simV ; `trm → simT }
 where
  simV : GRel₀^V
  simT : GRel₀^T
  simV {τ} = _[ simT {τ} ]^V_
  simT     = vcc-sim {`trm} {ε}
