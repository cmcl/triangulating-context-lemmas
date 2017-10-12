{---------------------------------------------}
{-- Contexts and observational approximation -}
{---------------------------------------------}
module obs-apx where

open import Level as L using (Level ; _⊔_)
open import Data.Product hiding (map)
open import Function as F hiding (_∋_ ; _$_)
open import Relation.Binary.PropositionalEquality as PEq using (_≡_)

open import lambda-fg
open import acmm
open import relations
open import sim-fusion-lemmas
open import big-step-prop

-- VSC Contexts; contextual equivalence
infixr 20 ⟪-_-⟫
infixr 20 _⟪_⟫
infixr 20 _⟪∘⟫_
infixr 20 _⟪∘_⟫_
infixr 20 VSC⟪_⊢_⟫

-- Corresponds to Definition 2.8 (K = VSC).

data VSC⟪_⊢_⟫ (Γ : Cx) (τ : Ty) : {f : CBV} → PreModel L.zero

 where

  `λ   : admits-λ λ {f} → VSC⟪ Γ ⊢ τ ⟫ {f}

  `exp : ∀ {f} {σ} → [ Exp {f} σ ⟶ VSC⟪ Γ ⊢ τ ⟫ {f} σ ]
    -- no holes; saves re-traversal

  ⟪-_-⟫ : [ Γ ⊨_  ⟶  VSC⟪ Γ ⊢ τ ⟫ {`trm} τ ]
    -- {Δ : Cx} → (ρ : Γ ⊨ Δ) → Cxt {Γ} {σ} σ Δ

  `val : {σ : Ty} → [ VSC⟪ Γ ⊢ τ ⟫ {`val} σ  ⟶  VSC⟪ Γ ⊢ τ ⟫ {`trm} σ ]
    -- lifting

  _`$_ : admits-$   λ {f} → VSC⟪ Γ ⊢ τ ⟫ {f}
  `if  : admits-if  λ {f} → VSC⟪ Γ ⊢ τ ⟫ {f}
  `let : admits-let λ {f} → VSC⟪ Γ ⊢ τ ⟫ {f}

-- Context instantiation

_⟪_⟫ : ∀ {f} {Γ Δ} {σ τ}
       (P : VSC⟪ Γ ⊢ σ ⟫ {f} τ Δ) (T : Trm σ Γ) → Exp {f} τ Δ

`exp E ⟪ T ⟫ =  E
`λ M   ⟪ T ⟫ = `λ (M ⟪ T ⟫)

⟪- ρ -⟫   ⟪ T ⟫ = subst T ρ

(`val V)  ⟪ T ⟫ = `val (V ⟪ T ⟫)

(V `$ W)  ⟪ T ⟫ = (V ⟪ T ⟫) `$ (W ⟪ T ⟫)
`if B L R ⟪ T ⟫ = `if  (B ⟪ T ⟫) (L ⟪ T ⟫) (R ⟪ T ⟫)
`let M N  ⟪ T ⟫ = `let (M ⟪ T ⟫) (N ⟪ T ⟫)

-- a distinguished example: action of Val substitution on contexts

substC : ∀ {f} {τ υ} {Γ Δ Ξ}
         (P : VSC⟪ Γ ⊢ τ ⟫ {f} υ Δ) → (ρ : Δ ⊨ Ξ) → VSC⟪ Γ ⊢ τ ⟫ {f} υ Ξ

substC (`exp E)      = `exp ∘ subst E
substC  (`λ M)       = `λ ∘ (substC M) ∘ ext₀^Env

substC ⟪- ρ' -⟫    ρ = ⟪- ρ *-Sub ρ' -⟫

substC (`val P)      = `val ∘ (substC P)
substC (F `$ A)    ρ = (substC F ρ) `$ (substC A ρ)
substC (`if B L R) ρ = `if (substC B ρ) (substC L ρ) (substC R ρ)
substC (`let P R)  ρ = `let (substC P ρ) (substC R (ext₀^Env ρ))

-- commutation between substitution and instantiation

_substC⟪_⟫_ : ∀ {f} {τ υ} {Γ Δ Ξ}
                (C : VSC⟪ Γ ⊢ τ ⟫ {f} υ Δ) (T : Trm τ Γ) (ρ : Δ ⊨ Ξ) →
 substC C ρ ⟪ T ⟫ ≡ subst (C ⟪ T ⟫) ρ

`exp E       substC⟪ T ⟫ ρ = PEq.refl
`λ M         substC⟪ T ⟫ ρ
 rewrite M substC⟪ T ⟫ (ext₀^Env ρ)
                           = PEq.refl

⟪- ρ' -⟫     substC⟪ T ⟫ ρ
 rewrite lemma33 ρ ρ' T    = PEq.refl
`val C         substC⟪ T ⟫ ρ
 rewrite C substC⟪ T ⟫ ρ   = PEq.refl
(F `$ A)     substC⟪ T ⟫ ρ
 rewrite F substC⟪ T ⟫ ρ | A substC⟪ T ⟫ ρ
                           = PEq.refl
`if B L R    substC⟪ T ⟫ ρ
 rewrite B substC⟪ T ⟫ ρ | L substC⟪ T ⟫ ρ | R substC⟪ T ⟫ ρ
                           = PEq.refl
`let P Q     substC⟪ T ⟫ ρ
 rewrite P substC⟪ T ⟫ ρ | Q substC⟪ T ⟫ (ext₀^Env ρ)
                           = PEq.refl

-- composition of contexts

_⟪∘⟫_ : ∀ {f} {Γ Δ Ξ} {σ τ υ}
          (P : VSC⟪ Δ ⊢ σ ⟫ {f} τ Ξ)
          (Q : VSC⟪ Γ ⊢ υ ⟫ {`trm} σ Δ) → VSC⟪ Γ ⊢ υ ⟫ {f} τ Ξ
`exp E     ⟪∘⟫ Q = `exp E
`λ M       ⟪∘⟫ Q = `λ (M ⟪∘⟫ Q)
⟪- ρ -⟫    ⟪∘⟫ Q =  substC Q ρ
`val P     ⟪∘⟫ Q = `val (P ⟪∘⟫ Q)
(F `$ A)   ⟪∘⟫ Q = F ⟪∘⟫ Q `$ A ⟪∘⟫ Q
`if B L R  ⟪∘⟫ Q = `if (B ⟪∘⟫ Q) (L ⟪∘⟫ Q) (R ⟪∘⟫ Q)
`let P R   ⟪∘⟫ Q = `let (P ⟪∘⟫ Q) (R ⟪∘⟫ Q)

-- commutation between composition and instantiation

_⟪∘_⟫_ : ∀ {f} {Γ Δ Ξ} {σ τ υ} (P : VSC⟪ Δ ⊢ σ ⟫ {f} τ Ξ) (T : Trm υ Γ) →
           (Q : VSC⟪ Γ ⊢ υ ⟫ {`trm} σ Δ) → (P ⟪∘⟫ Q) ⟪ T ⟫ ≡ P ⟪ Q ⟪ T ⟫ ⟫

`exp E    ⟪∘ T ⟫ Q = PEq.refl
`λ M      ⟪∘ T ⟫ Q rewrite M ⟪∘ T ⟫ Q = PEq.refl

⟪- ρ -⟫   ⟪∘ T ⟫ Q = Q substC⟪ T ⟫ ρ
`val P    ⟪∘ T ⟫ Q rewrite P ⟪∘ T ⟫ Q = PEq.refl
(F `$ A)  ⟪∘ T ⟫ Q rewrite F ⟪∘ T ⟫ Q | A ⟪∘ T ⟫ Q = PEq.refl
`if B L R ⟪∘ T ⟫ Q rewrite B ⟪∘ T ⟫ Q | L ⟪∘ T ⟫ Q | R ⟪∘ T ⟫ Q = PEq.refl
`let P R  ⟪∘ T ⟫ Q rewrite P ⟪∘ T ⟫ Q | R ⟪∘ T ⟫ Q = PEq.refl

-- Ground equivalence
-- The most boring relation of them all, but which ensures termination.
-- Moreover, it's an equivalence relation!

data gnd-eqv₀^B : GRel₀^B
 where
  gnd-eqv₀^B-b : ∀  {β} b → gnd-eqv₀^B {β} b b

data gnd-eqv₀^V : GRel₀^V
 where
  gnd-eqv₀^V-b :
    ∀  {β} {b b'} → gnd-eqv₀^B {β} b b' → gnd-eqv₀^V {`b β} (`b b) (`b b')

  gnd-eqv₀^V-λ : ∀ {σ τ} {M N} → gnd-eqv₀^V {σ `→ τ}  (`λ M)  (`λ N)

gnd-eqv₀^T : GRel₀^T
gnd-eqv₀^T {τ} = _[ gnd-eqv₀^V {τ} ]^T_

gnd-eqv₀ : GRel₀^E
gnd-eqv₀ {`val} = gnd-eqv₀^V
gnd-eqv₀ {`trm} = gnd-eqv₀^T

-- Properties of ground equivalence

{- a pattern
Lemma-XXX : (f : CBV) → Set
Lemma-XXX f = ?
lemma-XXX : ∀ {f} → Lemma-XXX f
lemma-XXX {f} = case f return Lemma-XXX of λ { `val →  prfV ; `trm → prfT  }
 where
  prfV : Lemma-XXX `val
  prfT : Lemma-XXX `trm
  prfV = ?
  prfT = ?
  lemma  : Lemma-XXX ?
  lemma  = ?
-}

gnd-eqv₀^B-refl-inv : {b b' : ⟦ `B ⟧B} → gnd-eqv₀ (`b b) (`b b') → b ≡ b'
gnd-eqv₀^B-refl-inv (gnd-eqv₀^V-b (gnd-eqv₀^B-b b)) = PEq.refl

Gnd-eqv₀-refl : (f : CBV) → Set
Gnd-eqv₀-refl f = ∀ {τ} E → gnd-eqv₀ {f} {τ} E E
gnd-eqv₀-refl : ∀ {f} → Gnd-eqv₀-refl f
gnd-eqv₀-refl {f} =
  case f return Gnd-eqv₀-refl of λ { `val →  prfV ; `trm → prfT }
 where
  prfV : Gnd-eqv₀-refl `val
  prfT : Gnd-eqv₀-refl `trm
  prfV  {`b β}  (`var ())
  prfV  {`b β}   (`b b)  = gnd-eqv₀^V-b (gnd-eqv₀^B-b b)

  prfV {σ `→ τ} (`var ())
  prfV {σ `→ τ}  (`λ M)  = gnd-eqv₀^V-λ {M = M} {N = M}

  prfT {τ} = lemma-[ prfV {τ} ]^T-refl

gnd-eqv₀^V-aux :
  ∀ {τ} {U V W} → gnd-eqv₀ U V → gnd-eqv₀ V W → gnd-eqv₀^V {τ} W U
gnd-eqv₀^V-aux  {`b β} (gnd-eqv₀^V-b (gnd-eqv₀^B-b b))
                       (gnd-eqv₀^V-b (gnd-eqv₀^B-b .b)) = gnd-eqv₀-refl (`b b)
gnd-eqv₀^V-aux {σ `→ τ} gnd-eqv₀^V-λ  gnd-eqv₀^V-λ  = gnd-eqv₀^V-λ

gnd-eqv₀^V-sym : ∀ {τ} {V W} → gnd-eqv₀ V W → gnd-eqv₀^V {τ} W V
gnd-eqv₀^V-sym {τ} {V = V} = gnd-eqv₀^V-aux {τ} (gnd-eqv₀-refl V)

Gnd-eqv₀-trans : (f : CBV) → Set
Gnd-eqv₀-trans f =
  ∀ {τ} {M N P} → gnd-eqv₀ M N → gnd-eqv₀ N P → gnd-eqv₀ {f} {τ} M P
gnd-eqv₀-trans : ∀ {f} → Gnd-eqv₀-trans f
gnd-eqv₀-trans {f} =
  case f return Gnd-eqv₀-trans of λ { `val →  prfV ; `trm → prfT  }
 where
  prfV : Gnd-eqv₀-trans `val
  prfT : Gnd-eqv₀-trans `trm
  prfV l r = gnd-eqv₀^V-sym (gnd-eqv₀^V-aux l r)
  prfT {τ} = lemma-[ prfV {τ} ]^T-trans

-- gnd-eqv₀^T is mostly a congruence
gnd-eqv₀^T-if :
  ∀ {σ} {B C M N P Q} → gnd-eqv₀ B C → gnd-eqv₀ M P → gnd-eqv₀ N Q →
    gnd-eqv₀^T {σ} (`if B M N) (`if C P Q)

gnd-eqv₀^T-if  = lemma-[-]^T-if {R = gnd-eqv₀^V} gnd-eqv₀^B-refl-inv

gnd-eqv₀^T-let : ∀ {σ τ} {M N P Q} → gnd-eqv₀^T {σ} M P →
 (∀ {V W} → gnd-eqv₀ V W → gnd-eqv₀ (N ⟨ V /var₀⟩) (Q ⟨ W /var₀⟩)) →
 gnd-eqv₀^T {τ} (`let M N) (`let P Q)
gnd-eqv₀^T-let = lemma-[-]^T-let {R = gnd-eqv₀^V}

-- an important lemma: at higher type, if P terminates, then so does Q
-- so it suffices to consider relations at higher-type on *values*
lemma-[-]^T-gnd-eqv₀-λ : {ℓ^V : Level} {R : {τ : Ty} → GRel^V {ℓ^V} {τ}} →
 ∀ {σ τ} {P Q} → (∀ {M N} → P ⇓ `λ M → Q ⇓ `λ N → R (`λ M) (`λ N)) →
 gnd-eqv₀ P Q → P [ R {σ `→ τ} ]^T Q
lemma-[-]^T-gnd-eqv₀-λ r-λ s {`var ()}
lemma-[-]^T-gnd-eqv₀-λ r-λ s  {`λ M}  derM with s derM
... | `var () , _
... | `λ N , derN , gnd-eqv₀^V-λ = `λ N , derN , r-λ derM derN

-- open extension of gnd-eqv₀
gnd-eqv : ∀ {f} {Γ} {υ} → Rel^E {f} {L.zero} {Γ} {υ}
gnd-eqv {f} = case f return (λ f → ∀ {Γ} {υ} → Rel^E {f} {_} {Γ} {υ})
 of λ { `val → gnd-eqvV ; `trm → gnd-eqvT }
 where
  gnd-eqvV : ∀ {Γ} {τ} → Rel^V {_} {Γ} {τ}
  gnd-eqvT : ∀ {Γ} {τ} → Rel^T {_} {Γ} {τ}
  gnd-eqvV {Γ} {τ} = _[ gnd-eqvT {Γ} {τ} ]^V_
  gnd-eqvT {Γ} {τ} = _[ gnd-eqv₀^T {τ} ]^O_

-- VSC approximation
-- The fundamental relations, quantifying over all VSC program contexts.

vsc-apx : ∀ {f} {Γ} {υ} → Rel^E {f} {L.zero} {Γ} {υ}
vsc-apx {f} = case f return (λ f → ∀ {Γ} {υ} → Rel^E {f} {_} {Γ} {υ})
 of λ { `val → apxV ; `trm → apxT }
 where
  apxV : ∀ {Γ} {τ} → Rel^V {_} {Γ} {τ}
  apxT : ∀ {Γ} {τ} → Rel^T {_} {Γ} {τ}
  apxV {Γ} {τ}     = _[ apxT {Γ} {τ} ]^V_
  apxT {Γ} {τ} M N =
    {υ : Ty} (P : VSC⟪ Γ ⊢ τ ⟫ υ ε) → gnd-eqv₀ {`trm} (P ⟪ M ⟫) (P ⟪ N ⟫)

-- open ground equivalence follows trivially: use the obvious context, the
-- hole itself!

vsc-apx→gnd-eqv^T : ∀ {Γ} {τ} {M N} → vsc-apx M N → gnd-eqv {`trm} {Γ} {τ} M N
vsc-apx→gnd-eqv^T sMN ρ = sMN P where P = ⟪- ρ -⟫

vsc-apx₀ : GRel₀^E
vsc-apx₀ {f} = case f return (λ f → ∀ {υ} → Rel^E {f} {_} {ε} {υ})
 of λ { `val → apxV ; `trm → apxT }
 where
  apxV : GRel₀^V
  apxT : GRel₀^T
  apxV {τ} = _[ apxT {τ} ]^V_
  apxT     = vsc-apx {`trm} {ε}
