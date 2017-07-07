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

Ren-ε : ∀ {Γ} {τ} {X : Set} → Γ ∙ τ ⊆ ε → X
Ren-ε ρ with var ρ ze
Ren-ε ρ | ()

boo : ∀ {Γ Δ} {τ} → Γ ⊆ Δ → Γ ⊆ Δ ∙ τ
var (boo ρ) v = su (var ρ v)

bar : ∀ {Γ Δ} {τ} → Γ ⊨ Δ → Γ ⊨ Δ ∙ τ
var (bar ρ) v = weak *-Var (var ρ v)

suc : ∀ {Γ Δ} {τ} → Γ ∙ τ ⊨ Δ → Γ ⊨ Δ
var (suc ρ) v = var ρ (su v)

zero : ∀ {Γ Δ} {τ} → Γ ∙ τ ⊨ Δ → Val τ Δ
zero ρ = var ρ ze

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
{-
  →βV-beta : {σ τ : Ty} {M : (σ ⊢ Trm τ) _} {V : _} →
            (βV M V) →βV (M ⟨ V /var₀⟩)
  →βV-trans : {σ τ : Ty} {M N P : Trm₀ τ} → M →βV N → N →βV P → M →βV P
-}
  →βV-step : {σ τ : Ty} {M : Trm₀ τ} {N : (σ ⊢ Trm τ) _} {V : _} →
    M →βV (`λ N `$ V) → M →βV (N ⟨ V /var₀⟩)

massive : ∀ {Γ} {σ τ} (ρ : Γ ⊨ ε) → (M : Trm σ (Γ ∙ τ)) → (V : Val₀ τ) →
  subst M (ext₀^Env ρ) ⟨ subst (Ren₀ *-Var V) ρ /var₀⟩ ≡ subst M (ρ `∙ V)
massive ρ M V = {!!}

betaV-Trm : ∀ {Γ} {σ} → (ρ : Γ ⊨ ε) → (M : Trm σ Γ) → βVΓ ρ M →βV subst M ρ
betaV-Trm   {ε}   ρ M rewrite PEq.sym (subst-equiv ρ M) = →βV-refl
betaV-Trm {Γ ∙ τ} ρ M with betaV-Trm (suc ρ) (βV M (Ren₀ *-Var zero ρ))
... | ih rewrite PEq.sym (subst-equiv ρ M) |
                 subst-equiv (suc ρ) (M ⟨ Ren₀ *-Var zero ρ /var₀⟩) = {!!}
{-
betaV-Trm {Γ ∙ τ} ρ M with betaV-Trm (suc ρ) (`λ M `$ (Ren₀ *-Var zero ρ))
... | ih = →βV-step {V = {!!}} {!ih!} -- rewrite massive (suc ρ) M (zero ρ)
-}

  -- rewrite PEq.sym (subst-equiv ρ M) |
  --         subst-equiv (suc ρ) (M ⟨ Ren₀ *-Var zero ρ /var₀⟩) = {!!}

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
--VCC-betaV {ε} ρ M C = PEq.refl
--VCC-betaV {Γ ∙ τ} ρ M C = {!VCC-betaV (suc ρ) (`λ !}

VCC-make : ∀ {Γ} {σ} → Γ ⊨ ε → VCC⟪ Γ ⊢ σ ⟫ {`trm} σ ε
VCC-make {Γ} ρ = VCC-sub {Γ} ⟪- refl^Var -⟫ ρ -- (VCC-Env Γ) ?

show-me : ∀ {Γ} {σ} {ρ : Γ ⊨ ε} {M : Trm σ Γ} {V} →
  subst-rho ρ M ⇓ V → ((VCC-sub ⟪- refl^Var -⟫ ρ) ⟪ M ⟫VCC) ⇓ V
show-me {ε} {ρ = ρ} {M = M} der rewrite ι^Var-lemma M = der
show-me {Γ ∙ τ} {ρ = ρ} {M = M} der = {!!}

Ren₀-lemma : ∀ {f} {σ} → (E : Exp₀ {f} σ) → (Ren₀ *-Var E) ≡ E
Ren₀-lemma E rewrite ι^Var-lemma E = PEq.refl

-- composition of valuations: ren-sub fusion
_*-RenSub_ : ∀ {Γ Δ Ξ} → (ρ : Δ ⊆ Ξ) → (ρ' : Γ ⊨ Δ) → Γ ⊨ Ξ
ρ *-RenSub ρ' = map-Env (ρ *-Var_) ρ'

lemma32 : ∀ {f} {Γ Δ Ξ} {σ} → (ρ : Δ ⊆ Ξ) → (ρ' : Γ ⊨ Δ) → (E : Exp {f} σ Γ) →
 ((ρ *-RenSub ρ') *-Val E) ≡ (ρ *-Var (ρ' *-Val E))
lemma32 ρ ρ' (`var v) = PEq.refl
lemma32 ρ ρ' (`b b)  = PEq.refl
lemma32 ρ ρ' (`λ M)  = PEq.cong λλ (lemma32 (ext₀^Var ρ) (ext₀^Env ρ') M)
lemma32 ρ ρ' (`val V) rewrite lemma32 ρ ρ' V = PEq.refl
lemma32 ρ ρ' (f `$ a) rewrite lemma32 ρ ρ' f | lemma32 ρ ρ' a = PEq.refl
lemma32 ρ ρ' (`if b l r) rewrite lemma32 ρ ρ' b | lemma32 ρ ρ' l |
                                 lemma32 ρ ρ' r = PEq.refl
lemma32 ρ ρ'  (`let M N) rewrite lemma32 ρ ρ' M =
  PEq.cong (`let _) (lemma32 (ext₀^Var ρ) (ext₀^Env ρ') N)

weak-sub : ∀ {f} {Γ} {σ τ} → (V : Val τ Γ) → (E : Exp {f} σ Γ) →
  subst (weak *-Var E) (ι^Env `∙ V) ≡ E
weak-sub V E rewrite lemma32 {!!} {!!} E = {!!} -- PEq.sym (ι^Env-lemma E)
--(ι^Env `∙ V)
{-
weak-sub : ∀ {f} {Γ} {σ τ} → (V : Val τ Γ) → (E : Exp {f} σ Γ) →
  subst (weak *-Var E) (ι^Env `∙ V) ≡ E
weak-sub V (`var v) = PEq.refl
weak-sub V (`b b) = PEq.refl
weak-sub V (`λ M) = {!!}
weak-sub V (`val M) rewrite weak-sub V M = PEq.refl
weak-sub V (F `$ A) rewrite weak-sub V F | weak-sub V A = PEq.refl
weak-sub V (`if B L R)
  rewrite weak-sub V B | weak-sub V L | weak-sub V R = PEq.refl
weak-sub V (`let M N) rewrite weak-sub V M = {!!}
-}

_,,_ : Cx → Cx → Cx
Γ ,, ε = Γ
Γ ,, (Δ ∙ τ) = (Γ ,, Δ) ∙ τ

pad-right : ∀ {Γ Δ} → Γ ⊆ Γ ,, Δ
var pad-right v = {!!}

pad-left : ∀ {Γ Δ} → Δ ⊆ Γ ,, Δ
var pad-left v = {!!}

push : ∀ {Γ Δ Ξ} → Δ ⊨ Ξ → Δ ,, Γ ⊨ Ξ ,, Γ
var (push {ε} ρ) v = var ρ v
var (push {Γ ∙ τ} ρ) ze = `var ze
var (push {Γ ∙ τ} ρ) (su v) = weak *-Var (var (push {Γ} ρ) v)

-- var (push {Δ = ε} {Ξ} ρ) v = `var v
-- var (push {Δ = Δ ∙ τ} ρ) ze = pad-left *-Var (var ρ ze)
-- var (push {Δ = Δ ∙ σ} ρ) (su v) = var (push (suc ρ)) v
{-
push-id : ∀ {Γ Δ Ξ} {σ} {v : Var σ Γ} (ρ : Δ ⊨ Ξ) →
  var (push {Γ} ρ) v ≡ `var v
push-id ρ = {!!}

-- sub-ren : ∀ {f} {Γ} {σ τ} →
--   (ρ : Γ ⊨ ε) → (r : Δ ⊆ Γ) → (V : Val τ Δ) → (E : Exp {f} σ Δ) →
--   (r *-Var E) ⟨ V /var₀⟩ ≡ E
-}


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
    {υ : Ty} (P : VCC⟪ Γ ⊢ τ ⟫ υ ε) →
       sim₀ {`trm} (P ⟪ M ⟫VCC) (P ⟪ N ⟫VCC)

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

app : ∀ {Γ Δ} {ω σ τ} → VCC⟪ Γ ∙ ω ⊢ τ ⟫ {`trm} σ (Δ ∙ ω) → Val ω Δ →
  VCC⟪ Γ ∙ ω ⊢ τ ⟫ {`trm} σ Δ
app cxt v = `λ cxt `$ `exp v

-- substC-VCC : ∀ {Γ Δ} {σ} → Δ ⊨ ε →
--   VCC⟪ Γ ⊢ σ ⟫ {`trm} (absT (bwd Δ) σ) ε → VCC⟪ Γ ⊢ σ ⟫ {`trm} σ ε
-- substC-VCC {Δ = ε} ρ cxt = cxt
-- substC-VCC {Δ = Δ ∙ x} ρ cxt =
--   substC-VCC (foo ρ) (`let cxt ((`exp (`var ze)) `$ (`exp (weak *-Var var ρ
--   ze))))

vcc-sim→sim^T : ∀ {Γ} {τ} {M N} → vcc-sim M N → sim {`trm} {Γ} {τ} M N
vcc-sim→sim^T {Γ} {τ} sMN ρ = {!sMN P!} --sMN P
  where P : VCC⟪ Γ ⊢ τ ⟫ τ ε
        P = VCC-sub ⟪- refl^Var -⟫ ρ

-- vcc-sim→sim^T {ε} {M = M} {N = N} sMN ρ
--   rewrite ι^Env₀-lemma ρ M | ι^Env₀-lemma ρ N with sMN ⟪- ι^Var -⟫
-- ... | prf rewrite ι^Var₀-lemma ι^Var M | ι^Var₀-lemma ι^Var N = prf
-- vcc-sim→sim^T {Γ ∙ x} {τ} sMN ρ with make {Γ} {Γ} {Γ} {τ} ι^Var
-- ... | cxt = {!!}

-- vcc-sim₀ : GRel₀^E
-- vcc-sim₀ {f} = case f return (λ f → ∀ {υ} → Rel^E {f} {_} {ε} {υ})
--  of λ { `val → simV ; `trm → simT }
--  where
--   simV : GRel₀^V
--   simT : GRel₀^T
--   simV {τ} = _[ simT {τ} ]^V_
--   simT     = vcc-sim {`trm} {ε}
