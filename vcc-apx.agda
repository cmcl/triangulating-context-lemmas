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

ext₀^Var-ext₀ : ∀ {Γ} {σ} → {ρ : Γ ⊆ Γ} → (∀ {τ} v → var ρ {τ} v ≡ v) →
 ∀ {τ} v → var (pop! {σ} {Γ} ρ) {τ} v ≡ v
ext₀^Var-ext₀ {Γ} {σ} {ρ} eq =
  [ P ][ PEq.refl ,,,  PEq.cong su ∘ eq ]
 where P = λ {τ} v → var (pop! {σ} {Γ} ρ) {τ} v ≡ v

-- ι^Env-lemma : ∀ {f} {Γ} {σ} → (E : Exp {f} σ Γ) → (ι^Env *-Val E) ≡ E
-- ι^Env-lemma = ι^Env-lemma-aux {ρ = ι^Env} (λ v → PEq.refl)

-- ι^Env₀-lemma : ∀ {f} {σ} → (ρ : Env₀ ε) (E : Exp₀ {f} σ) → (ρ *-Val E) ≡ E
-- ι^Env₀-lemma ρ = ι^Env-lemma-aux {ρ = ρ} (λ ())
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

-- Ren₀-lemma : ∀ {τ} → (M : Trm₀ τ) → (Ren₀ *-Var M) ≡ M
-- Ren₀-lemma (`val x) = {!!}
-- Ren₀-lemma (M `$ M₁) = {!!}
-- Ren₀-lemma (`if M M₁ M₂) = {!!}
-- Ren₀-lemma (`let M x) = {!!}


open-closed-rho : ∀ {σ} (ρ : Env₀ (ε ∙ σ)) →
 ∀ {τ} v → var ρ {τ} v ≡ var (ι^Env `∙ var ρ ze) v
open-closed-rho ρ ze = PEq.refl
open-closed-rho ρ (su ())

subst-one : ∀ {σ τ} → (ρ : Env₀ (ε ∙ σ)) → (M : Trm τ (ε ∙ σ)) →
  subst M ρ ≡ subst M (ι^Env `∙ var ρ ze)
subst-one ρ M = subst-ext M {ρ = ρ} {ρ' = (ι^Env `∙ var ρ ze)} (open-closed-rho ρ)

subst-suc : ∀ {Γ} {σ τ} → (ρ : Γ ∙ τ ⊨ ε) → (M : Trm σ (Γ ∙ τ)) →
  subst M ρ ≡ subst (M ⟨ Ren₀ *-Var zero ρ /var₀⟩) (suc ρ)
subst-suc {ε} ρ M rewrite subst-ext₀ (M ⟨ Ren₀ *-Var zero ρ /var₀⟩) (suc ρ) = {!!}
subst-suc {Γ ∙ x} ρ M = {!!}

-- data Shift : {Γ Δ : Cx} (ρ : Γ ⊨ Δ) → Set where
--   Empty : Shift `ε
--   PlusOne : Shift ρ

acxt : ∀ {τ σ ω} → ε ∙ τ ∙ σ ⊨ ε → VCC⟪ ε ∙ τ ∙ σ ⊢ ω ⟫ {`trm} ω ε
acxt ρ = `λ ((`λ ⟪- refl^Var -⟫) `$ `exp (weak *-Var (var ρ {!!}))) `$
  `exp (var ρ (su ze))

extend-hole : ∀ {f} {Γ Δ} {σ τ ω} → Γ ∙ σ ⊨ Δ →
  VCC⟪ Γ ⊢ τ ⟫ {f} ω Δ → VCC⟪ Γ ∙ σ ⊢ τ ⟫ {f} ω Δ
extend-hole ρ (`λ M) = `λ (extend-hole (bar ρ) M) --(weak *-Var )
extend-hole ρ (`exp E) = `exp E
extend-hole ρ ⟪- r -⟫ = `λ ⟪- pop! r -⟫ `$ `exp (var ρ ze)
extend-hole ρ (`val M) = `val (extend-hole ρ M)
extend-hole ρ (F `$ A) = extend-hole ρ F `$ extend-hole ρ A
extend-hole ρ (`if B L R) =
  `if (extend-hole ρ B) (extend-hole ρ L) (extend-hole ρ R)
extend-hole ρ (`let M N) = `let (extend-hole ρ M) (extend-hole (bar ρ) N)

_:+:_ : Ty → Cx → Cx
σ :+: ε = ε ∙ σ
σ :+: (Γ ∙ τ) = (σ :+: Γ) ∙ τ

data FCx : Cx → Set where
  FEmp : FCx ε
  FCons : (σ : Ty) → (Γ : Cx) → FCx (σ :+: Γ)

snoc : (Γ : Cx) → FCx Γ
snoc ε = FEmp
snoc (Γ ∙ σ) with snoc Γ
snoc (.ε ∙ σ) | FEmp = FCons σ ε
snoc (.(σ :+: Γ) ∙ τ) | FCons σ Γ = FCons σ (Γ ∙ τ)

data BwdSub : Cx → Set where
  BSEmp : BwdSub ε
  BSCons : ∀ {Γ Δ} {σ} → Val σ Δ → Γ ⊨ Δ → BwdSub (σ :+: Γ)

shift : ∀ {Γ Δ} → Γ ⊨ Δ → BwdSub Γ
shift {Γ} ρ with snoc Γ
shift ρ | FEmp = BSEmp
shift ρ | FCons σ Γ = {!!}

swp : ∀ {Γ} {σ τ} → Γ ∙ σ ∙ τ ⊆ Γ ∙ τ ∙ σ
var swp ze = su ze
var swp (su ze) = ze
var swp (su (su v)) = su (su v)

barC : ∀ {f} {Γ Δ} {σ τ ω} → VCC⟪ Γ ⊢ ω ⟫ {f} τ Δ →
  VCC⟪ Γ ∙ σ ⊢ ω ⟫ {f} τ (Δ ∙ σ)
barC {σ = σ} (`λ {ν} M) = `λ (renC (barC M) swp)
barC (`exp E) = `exp (weak *-Var E)
barC ⟪- r -⟫ = ⟪- pop! r -⟫
barC (`val C) = `val (barC C)
barC (F `$ A) = (barC F) `$ (barC A)
barC (`if B L R) = `if (barC B) (barC L) (barC R)
barC {σ = σ} (`let {ν} M N) = `let (barC M) (renC (barC N) swp)

substC-Trm : ∀ {f} {Γ} {σ τ ω} → (C : VCC⟪ Γ ⊢ σ ⟫ {f} τ ε) →
  (M : Trm σ (Γ ∙ ω)) → (V : Val₀ ω) →
  (barC C) ⟪ M ⟫VCC ⟨ V /var₀⟩ ≡ C ⟪ M ⟨ Ren₀ *-Var V /var₀⟩ ⟫VCC
substC-Trm (`λ N) M V = {!!}
substC-Trm (`exp E) M V = {!!}
substC-Trm ⟪- r -⟫ M V = {!!}
substC-Trm (`val C) M V = {!!}
substC-Trm (F `$ A) M V = {!!}
substC-Trm (`if B L R) M V = {!!}
substC-Trm (`let N P) M V = {!!}

λV-Cxt→ : ∀ {Γ} {σ τ ω} {W} → (C : VCC⟪ Γ ⊢ σ ⟫ {`trm} τ ε) →
  (M : Trm σ (Γ ∙ ω)) → (V : Val₀ ω) →
  (((`λ (barC C)) `$ (`exp V)) ⟪ M ⟫VCC) ⇓ W →
  (C ⟪ M ⟨ Ren₀ *-Var V /var₀⟩ ⟫VCC) ⇓ W
λV-Cxt→ (`exp E) M V (⇓app der) = {!!}
λV-Cxt→ ⟪- r -⟫ M V der = {!!}
λV-Cxt→ (`val C) M V (⇓app der) rewrite substC-Trm C M V = der
λV-Cxt→ (F `$ A) M V der = {!!}
λV-Cxt→ (`if B L R) M V der = {!!}
λV-Cxt→ (`let N P) M V der = {!!}

make-aux : ∀ {Γ Δ} {τ} → Γ ⊨ Δ → VCC⟪ Γ ⊢ τ ⟫ {`trm} τ Δ →
  VCC⟪ Γ ⊢ τ ⟫ {`trm} τ Δ
make-aux {ε} ρ C = C
make-aux {Γ ∙ x} ρV C = {!!}
  where ρ = suc ρV
        V = var ρV ze

make : ∀ {Γ Δ} {τ} → Γ ⊨ Δ → VCC⟪ Γ ⊢ τ ⟫ {`trm} τ Δ
make {ε} ρ = ⟪- Ren₀ -⟫
make {Γ ∙ σ} {τ} ρ with make {Γ} {τ} (suc ρ)
... | prf = extend-hole ρ prf

-- extend-hole-make : ∀ {Γ} {σ τ} → (ρ : Γ ∙ σ ⊨ ε) → (M : Trm τ (Γ ∙ σ)) →
--   ∀ {U} → (extend-hole ρ (make (suc ρ)) ⟪ M ⟫) ⇓ U → subst M ρ ⇓ U
-- extend-hole-make {ε} ρ M {U} (⇓app der) rewrite subst-one ρ M = {!!}
--  rewrite ι^Var-lemma-aux pop!-refl M | ι^Var-lemma (var ρ ze)
--  rewrite subst-ext M {ρ = ρ} {ρ' = (ι^Env `∙ var ρ ze)} (open-closed-rho ρ) = {!!}
--extend-hole-make {ε} ρ M (⇓app der) | PEq.refl = {!!}
--... | prf rewrite prf = {!!}= {!!}
-- subst-ext M {ρ = ρ} {ρ' = (ι^Env `∙ var ρ ze)} (open-closed-rho ρ)
-- extend-hole-make {Γ ∙ x} {σ} {τ} ρ M der with extend-hole-make {Γ} {x} {τ} (suc ρ)
-- ... | C = {!!}

makeProp : ∀ {Γ} {τ} → (ρ : Γ ⊨ ε) → (M : Trm τ Γ) → ∀ {U} →
  ((make ρ) ⟪ M ⟫VCC) ⇓ U → subst M ρ ⇓ U
makeProp {ε} ρ M der rewrite ι^Env₀-lemma ρ M | ι^Var-lemma M = der
makeProp {Γ ∙ x} ρ M der with var ρ ze
... | V with makeProp {Γ} (suc ρ) (M ⟨ Ren₀ *-Var V /var₀⟩)
... | prf = {!!}

{-
makeProp {ε} ρ M {U} {V} (⇓app der)
  rewrite lemma34 M ρ U | ι^Var-lemma-aux pop!-refl M | ι^Var-lemma U |
          ι^Env-lemma-aux {ρ = ext₀^Env ρ} (ext₀^Env-ext₀ {ρ = ρ} (λ ())) M = der
makeProp {Γ ∙ x} {σ} {τ} ρ M der with makeProp {Γ} {x} {σ} (foo ρ)
... | IH = {!!}
-}
--  |

-- abs-app : ∀ {Γ} {τ} → (ρ : Γ ⊨ ε) → (M : Trm τ Γ) →
--   (make {Γ} ρ) ⟪ M ⟫ ≡ subst M ρ
-- abs-app {ε} ρ M rewrite ι^Env₀-lemma ρ M = {!!}
-- abs-app {Γ ∙ x} {τ} ρ M with make {Γ} {ε} {τ} (foo ρ)
-- ... | prf = {!!}

-- a distinguished example: action of Val substitution on contexts
substC-VCC : ∀ {f} {τ υ} {Γ Δ Ξ}
         (P : VCC⟪ Γ ⊢ τ ⟫ {f} υ Δ) → (ρ : Δ ⊨ Ξ) → VCC⟪ Γ ⊢ τ ⟫ {f} υ Ξ

substC-VCC (`exp E)      = `exp ∘ subst E
substC-VCC  (`λ M)       = `λ ∘ (substC-VCC M) ∘ ext₀^Env

substC-VCC ⟪- r -⟫    ρ = make (r *-Env ρ)

substC-VCC (`val P)      = `val ∘ (substC-VCC P)
substC-VCC (F `$ A)    ρ = (substC-VCC F ρ) `$ (substC-VCC A ρ)
substC-VCC (`if B L R) ρ = `if (substC-VCC B ρ) (substC-VCC L ρ) (substC-VCC R ρ)
substC-VCC (`let P R)  ρ = `let (substC-VCC P ρ) (substC-VCC R (ext₀^Env ρ))

cxt-vcc : ∀ {f} {Γ Δ} {τ σ} → Cxt⟪ Γ ⊢ τ ⟫ {f} σ Δ → VCC⟪ Γ ⊢ τ ⟫ {f} σ Δ
cxt-vcc (`λ M) = `λ (cxt-vcc M)
cxt-vcc (`exp E) = `exp E
cxt-vcc ⟪- ρ -⟫ = substC-VCC ⟪- ι^Var -⟫ ρ
cxt-vcc (`val M) = `val (cxt-vcc M)
cxt-vcc (F `$ A) = (cxt-vcc F) `$ (cxt-vcc A)
cxt-vcc (`if B L R) = `if (cxt-vcc B) (cxt-vcc L) (cxt-vcc R)
cxt-vcc (`let M N) = `let (cxt-vcc M) (cxt-vcc N)

vcc-cxt : ∀ {f} {Γ Δ} {τ σ} → VCC⟪ Γ ⊢ τ ⟫ {f} σ Δ → Cxt⟪ Γ ⊢ τ ⟫ {f} σ Δ
vcc-cxt (`λ M) = `λ (vcc-cxt M)
vcc-cxt (`exp E) = `exp E
vcc-cxt ⟪- r -⟫ = ⟪- map-Env `var r -⟫
vcc-cxt (`val M) = `val (vcc-cxt M)
vcc-cxt (F `$ A) = (vcc-cxt F) `$ (vcc-cxt A)
vcc-cxt (`if B L R) = `if (vcc-cxt B) (vcc-cxt L) (vcc-cxt R)
vcc-cxt (`let M N) = `let (vcc-cxt M) (vcc-cxt N)

{-
-- commutation between substitution and instantiation

_substC-VCC⟪_⟫_ : ∀ {f} {τ υ} {Γ Δ Ξ}
                (C : VCC⟪ Γ ⊢ τ ⟫ {f} υ Δ) (T : Trm τ Γ) (ρ : Δ ⊨ Ξ) →
 substC-VCC C ρ ⟪ T ⟫ ≡ subst (C ⟪ T ⟫) ρ

`exp E       substC-VCC⟪ T ⟫ ρ = PEq.refl
`λ M         substC-VCC⟪ T ⟫ ρ -- = PEq.cong `λ (M substC-VCC⟪ T ⟫ (ext₀^Env ρ))
 rewrite M substC-VCC⟪ T ⟫ (ext₀^Env ρ)
                           = PEq.refl

⟪- r -⟫     substC-VCC⟪ T ⟫ ρ
 rewrite lemma33 ρ ρ' T    = PEq.refl
`val C         substC-VCC⟪ T ⟫ ρ
 rewrite C substC-VCC⟪ T ⟫ ρ   = PEq.refl
(F `$ A)     substC-VCC⟪ T ⟫ ρ
 rewrite F substC-VCC⟪ T ⟫ ρ | A substC-VCC⟪ T ⟫ ρ
                           = PEq.refl
`if B L R    substC-VCC⟪ T ⟫ ρ
 rewrite B substC-VCC⟪ T ⟫ ρ | L substC-VCC⟪ T ⟫ ρ | R substC-VCC⟪ T ⟫ ρ
                           = PEq.refl
`let P Q     substC-VCC⟪ T ⟫ ρ
 rewrite P substC-VCC⟪ T ⟫ ρ | Q substC-VCC⟪ T ⟫ (ext₀^Env ρ)
                           = PEq.refl

-}

-- composition of contexts


-- commutation between composition and instantiation
{-
_⟪∘_⟫_ : ∀ {f} {Γ Δ Ξ} {σ τ υ} (P : VCC⟪ Δ ⊢ σ ⟫ {f} τ Ξ) (T : Trm υ Γ) →
           (Q : VCC⟪ Γ ⊢ υ ⟫ {`trm} σ Δ) → (P ⟪∘⟫ Q) ⟪ T ⟫ ≡ P ⟪ Q ⟪ T ⟫ ⟫

`exp E    ⟪∘ T ⟫ Q = PEq.refl
`λ M      ⟪∘ T ⟫ Q rewrite M ⟪∘ T ⟫ Q = PEq.refl

⟪- ρ -⟫   ⟪∘ T ⟫ Q = Q substC-VCC⟪ T ⟫ ρ
`val P    ⟪∘ T ⟫ Q rewrite P ⟪∘ T ⟫ Q = PEq.refl
(F `$ A)  ⟪∘ T ⟫ Q rewrite F ⟪∘ T ⟫ Q | A ⟪∘ T ⟫ Q = PEq.refl
`if B L R ⟪∘ T ⟫ Q rewrite B ⟪∘ T ⟫ Q | L ⟪∘ T ⟫ Q | R ⟪∘ T ⟫ Q = PEq.refl
`let P R  ⟪∘ T ⟫ Q rewrite P ⟪∘ T ⟫ Q | R ⟪∘ T ⟫ Q = PEq.refl
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
       sim₀ {`trm} ((vcc-cxt P) ⟪ M ⟫) ((vcc-cxt P) ⟪ N ⟫)

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

vcc-sim→cxt-sim : ∀ {Γ} {τ} {M N} → vcc-sim {`trm} {Γ} {τ} M N → cxt-sim M N
vcc-sim→cxt-sim sMN C with sMN (cxt-vcc C)
... | prf = {!!}

vcc-sim→sim^T : ∀ {Γ} {τ} {M N} → vcc-sim M N → sim {`trm} {Γ} {τ} M N
vcc-sim→sim^T {Γ} {τ} sMN ρ = {!!} --sMN P
  where P : VCC⟪ Γ ⊢ τ ⟫ τ ε
        P = make ρ

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
