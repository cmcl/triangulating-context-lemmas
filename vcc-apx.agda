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

_⟪_⟫ : ∀ {f} {Γ Δ} {σ τ}
       (P : VCC⟪ Γ ⊢ σ ⟫ {f} τ Δ) (T : Trm σ Γ) → Exp {f} τ Δ

`exp E ⟪ T ⟫ =  E
`λ M   ⟪ T ⟫ = `λ (M ⟪ T ⟫)

⟪- r -⟫   ⟪ T ⟫ = r *-Var T

(`val V)  ⟪ T ⟫ = `val (V ⟪ T ⟫)

(V `$ W)  ⟪ T ⟫ = (V ⟪ T ⟫) `$ (W ⟪ T ⟫)
`if B L R ⟪ T ⟫ = `if  (B ⟪ T ⟫) (L ⟪ T ⟫) (R ⟪ T ⟫)
`let M N  ⟪ T ⟫ = `let (M ⟪ T ⟫) (N ⟪ T ⟫)


Ren₀ : ∀ {Γ} → ε ⊆ Γ
var Ren₀ ()

Ren-ε : ∀ {Γ} {τ} {X : Set} → Γ ∙ τ ⊆ ε → X
Ren-ε ρ with var ρ ze
Ren-ε ρ | ()

boo : ∀ {Γ Δ} {τ} → Γ ⊆ Δ → Γ ⊆ Δ ∙ τ
var (boo ρ) v = su (var ρ v)

bar : ∀ {Γ Δ} {τ} → Γ ⊨ Δ → Γ ⊨ Δ ∙ τ
var (bar ρ) v = weak *-Var (var ρ v)

foo : ∀ {Γ Δ} {τ} → Γ ∙ τ ⊨ Δ → Γ ⊨ Δ
var (foo ρ) v = var ρ (su v)

faa : ∀ {Γ Δ} {τ} → Δ ∙ τ ⊆ Γ → Δ ⊆ Γ
var (faa ρ) v = var ρ (su v)

renC : ∀ {f} {Γ Δ Δ'} {σ τ} → VCC⟪ Γ ⊢ σ ⟫ {f} τ Δ → Δ ⊆ Δ' →
  VCC⟪ Γ ⊢ σ ⟫ {f} τ Δ'
renC (`λ M) = (`λ ∘ (renC M) ∘ ext₀^Var)
renC (`exp M) ρ = `exp (ρ *-Var M)
renC ⟪- r -⟫ ρ = ⟪- trans^Var r ρ -⟫
renC (`val P) = `val ∘ (renC P)
renC (F `$ A) ρ = (renC F ρ) `$ (renC A ρ)
renC (`if B L R) ρ = `if (renC B ρ) (renC L ρ) (renC R ρ)
renC (`let M N) ρ = `let (renC M ρ) (renC N (ext₀^Var ρ))

extend-hole : ∀ {f} {Γ Δ} {σ τ ω} → Γ ∙ σ ⊨ Δ →
  VCC⟪ Γ ⊢ τ ⟫ {f} ω Δ → VCC⟪ Γ ∙ σ ⊢ τ ⟫ {f} ω Δ
extend-hole ρ (`λ M) = `λ (extend-hole (bar ρ) M) --(weak *-Var )
extend-hole ρ (`exp E) = `exp E
extend-hole ρ ⟪- r -⟫ = `λ ⟪- pop! r -⟫ `$ (renC (`exp (var ρ ze)) refl^Var)
extend-hole ρ (`val M) = `val (extend-hole ρ M)
extend-hole ρ (F `$ A) = extend-hole ρ F `$ extend-hole ρ A
extend-hole ρ (`if B L R) =
  `if (extend-hole ρ B) (extend-hole ρ L) (extend-hole ρ R)
extend-hole ρ (`let M N) = `let (extend-hole ρ M) (extend-hole (bar ρ) N)

make : ∀ {Γ Δ} {τ} → Γ ⊨ Δ → VCC⟪ Γ ⊢ τ ⟫ {`trm} τ Δ
make {ε} ρ = ⟪- Ren₀ -⟫
make {Γ ∙ σ} {τ} ρ with make {Γ} {τ} (foo ρ)
... | prf = extend-hole ρ prf

Ren₀-lemma : ∀ {τ} → (M : Trm₀ τ) → (Ren₀ *-Var M) ≡ M
Ren₀-lemma (`val x) = {!!}
Ren₀-lemma (M `$ M₁) = {!!}
Ren₀-lemma (`if M M₁ M₂) = {!!}
Ren₀-lemma (`let M x) = {!!}

abs-app : ∀ {Γ} {τ} → (ρ : Γ ⊨ ε) → (M : Trm τ Γ) →
  (make {Γ} ρ) ⟪ M ⟫ ≡ subst M ρ
abs-app {ε} ρ M rewrite ι^Env₀-lemma ρ M = {!!}
abs-app {Γ ∙ x} {τ} ρ M with make {Γ} {ε} {τ} (foo ρ)
... | prf = {!!}

-- a distinguished example: action of Val substitution on contexts
substC : ∀ {f} {τ υ} {Γ Δ Ξ}
         (P : VCC⟪ Γ ⊢ τ ⟫ {f} υ Δ) → (ρ : Δ ⊨ Ξ) → VCC⟪ Γ ⊢ τ ⟫ {f} υ Ξ

substC (`exp E)      = `exp ∘ subst E
substC  (`λ M)       = `λ ∘ (substC M) ∘ ext₀^Env

substC ⟪- r -⟫    ρ = make (r *-Env ρ)

substC (`val P)      = `val ∘ (substC P)
substC (F `$ A)    ρ = (substC F ρ) `$ (substC A ρ)
substC (`if B L R) ρ = `if (substC B ρ) (substC L ρ) (substC R ρ)
substC (`let P R)  ρ = `let (substC P ρ) (substC R (ext₀^Env ρ))

{-
-- commutation between substitution and instantiation

_substC⟪_⟫_ : ∀ {f} {τ υ} {Γ Δ Ξ}
                (C : VCC⟪ Γ ⊢ τ ⟫ {f} υ Δ) (T : Trm τ Γ) (ρ : Δ ⊨ Ξ) →
 substC C ρ ⟪ T ⟫ ≡ subst (C ⟪ T ⟫) ρ

`exp E       substC⟪ T ⟫ ρ = PEq.refl
`λ M         substC⟪ T ⟫ ρ -- = PEq.cong `λ (M substC⟪ T ⟫ (ext₀^Env ρ))
 rewrite M substC⟪ T ⟫ (ext₀^Env ρ)
                           = PEq.refl

⟪- r -⟫     substC⟪ T ⟫ ρ
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

-}

-- composition of contexts

_⟪∘⟫_ : ∀ {f} {Γ Δ Ξ} {σ τ υ}
          (P : VCC⟪ Δ ⊢ σ ⟫ {f} τ Ξ)
          (Q : VCC⟪ Γ ⊢ υ ⟫ {`trm} σ Δ) → VCC⟪ Γ ⊢ υ ⟫ {f} τ Ξ
`exp E     ⟪∘⟫ Q = `exp E
`λ M       ⟪∘⟫ Q = `λ (M ⟪∘⟫ Q)
⟪- r -⟫    ⟪∘⟫ Q =  substC Q (r *-Env ι^Env)
`val P     ⟪∘⟫ Q = `val (P ⟪∘⟫ Q)
(F `$ A)   ⟪∘⟫ Q = F ⟪∘⟫ Q `$ A ⟪∘⟫ Q
`if B L R  ⟪∘⟫ Q = `if (B ⟪∘⟫ Q) (L ⟪∘⟫ Q) (R ⟪∘⟫ Q)
`let P R   ⟪∘⟫ Q = `let (P ⟪∘⟫ Q) (R ⟪∘⟫ Q)

-- commutation between composition and instantiation
{-
_⟪∘_⟫_ : ∀ {f} {Γ Δ Ξ} {σ τ υ} (P : VCC⟪ Δ ⊢ σ ⟫ {f} τ Ξ) (T : Trm υ Γ) →
           (Q : VCC⟪ Γ ⊢ υ ⟫ {`trm} σ Δ) → (P ⟪∘⟫ Q) ⟪ T ⟫ ≡ P ⟪ Q ⟪ T ⟫ ⟫

`exp E    ⟪∘ T ⟫ Q = PEq.refl
`λ M      ⟪∘ T ⟫ Q rewrite M ⟪∘ T ⟫ Q = PEq.refl

⟪- ρ -⟫   ⟪∘ T ⟫ Q = Q substC⟪ T ⟫ ρ
`val P    ⟪∘ T ⟫ Q rewrite P ⟪∘ T ⟫ Q = PEq.refl
(F `$ A)  ⟪∘ T ⟫ Q rewrite F ⟪∘ T ⟫ Q | A ⟪∘ T ⟫ Q = PEq.refl
`if B L R ⟪∘ T ⟫ Q rewrite B ⟪∘ T ⟫ Q | L ⟪∘ T ⟫ Q | R ⟪∘ T ⟫ Q = PEq.refl
`let P R  ⟪∘ T ⟫ Q rewrite P ⟪∘ T ⟫ Q | R ⟪∘ T ⟫ Q = PEq.refl
-}
-- Ground simulation
-- The most boring relation of them all, but which ensures termination.
-- Moreover, it's an equivalence relation!

data sim₀^B : GRel₀^B
 where
  sim₀^B-b : ∀  {β} b → sim₀^B {β} b b

data sim₀^V : GRel₀^V
 where
  sim₀^V-b : ∀  {β} {b b'} → sim₀^B {β} b b' → sim₀^V {`b β} (`b b) (`b b')

  sim₀^V-λ : ∀ {σ τ} {M N} → sim₀^V {σ `→ τ}  (`λ M)  (`λ N)

sim₀^T : GRel₀^T
sim₀^T {τ} = _[ sim₀^V {τ} ]^T_

sim₀ : GRel₀^E
sim₀ {`val} = sim₀^V
sim₀ {`trm} = sim₀^T

sim₀^B-refl-inv : {b b' : ⟦ `B ⟧B} → sim₀ (`b b) (`b b') → b ≡ b'
sim₀^B-refl-inv (sim₀^V-b (sim₀^B-b b)) = PEq.refl

Sim₀-refl : (f : CBV) → Set
Sim₀-refl f = ∀ {τ} E → sim₀ {f} {τ} E E
sim₀-refl : ∀ {f} → Sim₀-refl f
sim₀-refl {f} = case f return Sim₀-refl of λ { `val →  prfV ; `trm → prfT }
 where
  prfV : Sim₀-refl `val
  prfT : Sim₀-refl `trm
  prfV  {`b β}  (`var ())
  prfV  {`b β}   (`b b)  = sim₀^V-b (sim₀^B-b b)

  prfV {σ `→ τ} (`var ())
  prfV {σ `→ τ}  (`λ M)  = sim₀^V-λ {M = M} {N = M}

  prfT {τ} = lemma-[ prfV {τ} ]^T-refl

sim₀^V-aux : ∀ {τ} {U V W} → sim₀ U V → sim₀ V W → sim₀^V {τ} W U
sim₀^V-aux  {`b β} (sim₀^V-b (sim₀^B-b b)) (sim₀^V-b (sim₀^B-b .b)) =
  sim₀-refl (`b b)
sim₀^V-aux {σ `→ τ}     sim₀^V-λ                sim₀^V-λ            = sim₀^V-λ

sim₀^V-sym : ∀ {τ} {V W} → sim₀ V W → sim₀^V {τ} W V
sim₀^V-sym {τ} {V = V} = sim₀^V-aux {τ} (sim₀-refl V)

Sim₀-trans : (f : CBV) → Set
Sim₀-trans f = ∀ {τ} {M N P} → sim₀ M N → sim₀ N P → sim₀ {f} {τ} M P
sim₀-trans : ∀ {f} → Sim₀-trans f
sim₀-trans {f} = case f return Sim₀-trans of λ { `val →  prfV ; `trm → prfT  }
 where
  prfV : Sim₀-trans `val
  prfT : Sim₀-trans `trm
  prfV l r = sim₀^V-sym (sim₀^V-aux l r)
  prfT {τ} = lemma-[ prfV {τ} ]^T-trans

-- sim₀^T is mostly a congruence
sim₀^T-if : ∀ {σ} {B C M N P Q} → sim₀ B C → sim₀ M P → sim₀ N Q →
 sim₀^T {σ} (`if B M N) (`if C P Q)

sim₀^T-if  = lemma-[-]^T-if {R = sim₀^V} sim₀^B-refl-inv

sim₀^T-let : ∀ {σ τ} {M N P Q} → sim₀^T {σ} M P →
 (∀ {V W} → sim₀ V W → sim₀ (N ⟨ V /var₀⟩) (Q ⟨ W /var₀⟩)) →
 sim₀^T {τ} (`let M N) (`let P Q)
sim₀^T-let = lemma-[-]^T-let {R = sim₀^V}

-- the *most* important lemma: at higher type, if P terminates, then so does Q
-- so it suffices to consider relations at higher-type on *values*
lemma-[-]^T-sim₀-λ : {ℓ^V : Level} {R : {τ : Ty} → GRel^V {ℓ^V} {τ}} →
 ∀ {σ τ} {P Q} → (∀ {M N} → P ⇓ `λ M → Q ⇓ `λ N → R (`λ M) (`λ N)) →
 sim₀ P Q → P [ R {σ `→ τ} ]^T Q
lemma-[-]^T-sim₀-λ r-λ s {`var ()}
lemma-[-]^T-sim₀-λ r-λ s  {`λ M}  derM with s derM
... | `var () , _
... | `λ N , derN , sim₀^V-λ = `λ N , derN , r-λ derM derN

-- open extension of sim₀
sim : ∀ {f} {Γ} {υ} → Rel^E {f} {L.zero} {Γ} {υ}
sim {f} = case f return (λ f → ∀ {Γ} {υ} → Rel^E {f} {_} {Γ} {υ})
 of λ { `val → simV ; `trm → simT }
 where
  simV : ∀ {Γ} {τ} → Rel^V {_} {Γ} {τ}
  simT : ∀ {Γ} {τ} → Rel^T {_} {Γ} {τ}
  simV {Γ} {τ} = _[ simT {Γ} {τ} ]^V_
  simT {Γ} {τ} = _[ sim₀^T {τ} ]^O_

-- Contextual simulation/Observational approximation
-- The fundamental relations, quantifying over all program contexts.

vcc-sim : ∀ {f} {Γ} {υ} → Rel^E {f} {L.zero} {Γ} {υ}
vcc-sim {f} = case f return (λ f → ∀ {Γ} {υ} → Rel^E {f} {_} {Γ} {υ})
 of λ { `val → simV ; `trm → simT }
 where
  simV : ∀ {Γ} {τ} → Rel^V {_} {Γ} {τ}
  simT : ∀ {Γ} {τ} → Rel^T {_} {Γ} {τ}
  simV {Γ} {τ}     = _[ simT {Γ} {τ} ]^V_
  simT {Γ} {τ} M N =
    {υ : Ty} (P : VCC⟪ Γ ⊢ τ ⟫ υ ε) → sim₀ {`trm} (P ⟪ M ⟫) (P ⟪ N ⟫)

-- open simulation follows trivially: use the obvious context, the hole
-- itself!

bwd : Cx → List Ty
bwd ε = []
bwd (Γ ∙ τ) = τ ∷ bwd Γ

absT : List Ty → Ty → Ty
absT [] σ = σ
absT (τ ∷ Γ) σ = τ `→ (absT Γ σ)

cxT : Cx → Cx
cxT ε = ε
cxT (Γ ∙ τ) = Γ ∙ τ ∙ τ

holeT : Cx → Ty → Ty
holeT ε σ = σ
holeT (Γ ∙ τ) σ = τ `→ σ

ι^Var-lemma-aux : {Γ : Cx} {σ : Ty} {ρ : Γ ⊆ Γ}
             (prf : {τ : Ty} (v : Var τ Γ) → var ρ {τ} v ≡ v) →
             {cbv : CBV} (E : Exp {cbv} σ Γ) →
             (ρ *-Var E) ≡ E
ι^Var-lemma-aux prf  (`var v)
 rewrite prf v             = PEq.refl
ι^Var-lemma-aux prf   (`b b)    = PEq.refl
ι^Var-lemma-aux prf   (`λ M) = {!!}
-- rewrite ι^Var-lemma-aux (ext₀^Env-ext₀ prf) M    = PEq.refl
ι^Var-lemma-aux prf  (`val V)
 rewrite ι^Var-lemma-aux prf V  = PEq.refl
ι^Var-lemma-aux prf  (F `$ A)
 rewrite ι^Var-lemma-aux prf F | ι^Var-lemma-aux prf A = PEq.refl
ι^Var-lemma-aux prf (`if B L R)
  rewrite ι^Var-lemma-aux prf B | ι^Var-lemma-aux prf L |
          ι^Var-lemma-aux prf R = PEq.refl
ι^Var-lemma-aux prf  (`let M N) = {!!}

ι^Var-lemma : ∀ {f} {Γ} {σ} → (E : Exp {f} σ Γ) → (ι^Var *-Var E) ≡ E
ι^Var-lemma = ι^Var-lemma-aux {ρ = ι^Var} (λ v → PEq.refl)

ι^Var₀-lemma : ∀ {f} {σ} → (ρ : ε ⊆ ε) (E : Exp₀ {f} σ) → (ρ *-Var E) ≡ E
ι^Var₀-lemma ρ = ι^Var-lemma-aux {ρ = ρ} (λ ())

app : ∀ {Γ Δ} {ω σ τ} → VCC⟪ Γ ∙ ω ⊢ τ ⟫ {`trm} σ (Δ ∙ ω) → Val ω Δ →
  VCC⟪ Γ ∙ ω ⊢ τ ⟫ {`trm} σ Δ
app cxt v = `λ cxt `$ `exp v

-- substC : ∀ {Γ Δ} {σ} → Δ ⊨ ε →
--   VCC⟪ Γ ⊢ σ ⟫ {`trm} (absT (bwd Δ) σ) ε → VCC⟪ Γ ⊢ σ ⟫ {`trm} σ ε
-- substC {Δ = ε} ρ cxt = cxt
-- substC {Δ = Δ ∙ x} ρ cxt =
--   substC (foo ρ) (`let cxt ((`exp (`var ze)) `$ (`exp (weak *-Var var ρ
--   ze))))

vcc-sim→sim^T : ∀ {Γ} {τ} {M N} → vcc-sim M N → sim {`trm} {Γ} {τ} M N
vcc-sim→sim^T {Γ} {τ} sMN ρ = {!!} --sMN (make ρ) --{!make ρ!}
  where P : VCC⟪ Γ ⊢ τ ⟫ τ ε
        P = make ρ

-- vcc-sim→sim^T {ε} {M = M} {N = N} sMN ρ
--   rewrite ι^Env₀-lemma ρ M | ι^Env₀-lemma ρ N with sMN ⟪- ι^Var -⟫
-- ... | prf rewrite ι^Var₀-lemma ι^Var M | ι^Var₀-lemma ι^Var N = prf
-- vcc-sim→sim^T {Γ ∙ x} {τ} sMN ρ with make {Γ} {Γ} {Γ} {τ} ι^Var
-- ... | cxt = {!!}

vcc-sim₀ : GRel₀^E
vcc-sim₀ {f} = case f return (λ f → ∀ {υ} → Rel^E {f} {_} {ε} {υ})
 of λ { `val → simV ; `trm → simT }
 where
  simV : GRel₀^V
  simT : GRel₀^T
  simV {τ} = _[ simT {τ} ]^V_
  simT     = vcc-sim {`trm} {ε}
