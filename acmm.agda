{----------------------------------------------}
{- Semantics and Generic Evaluation Functions -}
{----------------------------------------------}
module acmm where

open import Level as L using (Level ; _⊔_)
open import Function as F hiding (_∋_ ; _$_)
open import Relation.Binary.PropositionalEquality as PEq using (_≡_)

open import lambda-fg

record Morphism {ℓ^V ℓ^T : Level}
 {𝓥 : PreModel ℓ^V} (Θ : Model 𝓥) (𝓣 : PreModel ℓ^T) : Set (ℓ^V ⊔ ℓ^T)
 where
  constructor mkMorphism
  field inj : PreMorphism 𝓥 𝓣

ι^Inj : {ℓ : Level} {𝓥 : PreModel ℓ} {Θ : Model 𝓥} → Morphism Θ 𝓥
ι^Inj = mkMorphism id

Val→Trm : PreMorphism Exp Exp -- Val Trm
Val→Trm = `val

record Semantics {ℓ^V ℓ^E : Level}
 {𝓥 : PreModel ℓ^V} {Θ : Model 𝓥} -- the variables
 {𝓔 : {f : CBV} → PreModel ℓ^E}
 (var : Morphism Θ (𝓔 {`val})) -- the injection of variables into values
 (val : PreMorphism (𝓔 {`val}) (𝓔 {`trm}) )
   -- the morphism from values into terms
 : Set (ℓ^E ⊔ ℓ^V)
 where

  𝓔𝓥 = 𝓔 {`val}
  𝓔𝓣 = 𝓔 {`trm}

-- Semantics give (R)HOAS types to ⟦λ⟧ and ⟦let⟧

  infixl 5 _⟦$⟧_
  field
    ⟦λ⟧    : {σ τ : Ty} → [ □ (𝓥 σ ⟶ 𝓔𝓣 τ) ⟶ 𝓔𝓥 (σ `→ τ) ]
    ⟦b⟧    : {β : BTy} → (b : ⟦ β ⟧B) →  [       𝓔𝓥 (`b β)  ]

  field
    _⟦$⟧_  : {σ τ : Ty} → [ 𝓔𝓥 (σ `→ τ) ⟶ 𝓔𝓥 σ ⟶  𝓔𝓣 τ  ]
    ⟦if⟧   : {σ : Ty} →   [ 𝓔𝓥 (`b `B) ⟶ 𝓔𝓣 σ ⟶ 𝓔𝓣 σ ⟶ 𝓔𝓣 σ ]
    ⟦let⟧  : {σ τ : Ty} → [ 𝓔𝓣 σ ⟶  □ (𝓥 σ ⟶ 𝓔𝓣 τ)  ⟶ 𝓔𝓣 τ ]

-- The generic traversal which drives everything.

module Eval {ℓ^V ℓ^E : Level}
 {𝓥 : PreModel ℓ^V} {Θ : Model 𝓥}           -- the variables
 {𝓔 : {f : CBV} → PreModel ℓ^E} {VAR : Morphism Θ (𝓔 {`val})} -- the values
 {VAL : PreMorphism (𝓔 {`val}) (𝓔 {`trm})}
   -- the injection of values into terms
 (𝓢 : Semantics {Θ = Θ} {𝓔 = λ {f} → 𝓔 {f}} VAR VAL) where
 open Thin Θ
 open Semantics 𝓢

 sem : ∀ {f} {Γ} → [ (Γ -Env) 𝓥 ⟶ (Γ -⟦ f ⟧) (𝓔 {f}) ]

 sem ρ (`var v) = inj (var ρ v) where open Morphism VAR
 sem ρ (`b b)   = ⟦b⟧ b

 sem {`val} {Γ} {Δ} ρ (`λ {σ} {τ} t)     = ⟦λ⟧ ⟦t⟧
  where
   ⟦t⟧ : □ (𝓥 σ ⟶ 𝓔𝓣 τ) Δ -- ∀ {Θ} → (Δ ⊆ Θ) → (𝓔 σ Θ) → 𝓣 τ Θ
   ⟦t⟧ {Θ} inc u = sem (ext ρ inc u) t

 sem ρ (`val v)    = VAL (sem ρ v)
 sem ρ (t `$ u)    = sem ρ t ⟦$⟧ sem ρ u
 sem ρ (`if b l r) = ⟦if⟧ (sem ρ b) (sem ρ l) (sem ρ r)

 sem {`trm} {Γ} {Δ} ρ (`let {σ} {τ} M N) = ⟦let⟧ (sem ρ M) ⟦N⟧
  where
   ⟦N⟧ :  □ (𝓥 σ ⟶ 𝓔𝓣 τ) Δ
   ⟦N⟧ {Θ} inc u = sem (ext ρ inc u) N

syntactic : {ℓ^V : Level} {𝓥 : PreModel ℓ^V} {Θ : Model 𝓥}
 (mod : Model₀ Θ) {VAR : Morphism Θ Val} →
 Semantics {Θ = Θ} {𝓔 = λ {f} → Exp {f}} VAR Val→Trm -- the Trm part gets to
                                                     -- tag along `for free'
syntactic mod {VAR} = record
  { ⟦λ⟧  = λ t → `λ (t weak var₀)
  ; ⟦b⟧ = `b
  ; _⟦$⟧_ = _`$_
  ; ⟦if⟧  = `if
  ; ⟦let⟧  = λ M N → `let M (N weak var₀)
  } where open Model₀ mod

{-- Some traversals -}

--Renaming

Var→Val : Morphism 𝓥ar Val
Var→Val = mkMorphism `var

Renaming : Semantics Var→Val Val→Trm
Renaming = syntactic 𝓥ar₀

infix 4 _*-Var_

_*-Var_ : ∀ {f} {Γ Δ} → (inc : Γ ⊆ Δ) →
          {σ : Ty} (t : Exp {f} σ Γ) → Exp {f} σ Δ
inc *-Var t = sem inc t where open Eval Renaming

th^Val : ∀ {σ} → Thinnable (Val σ)
th^Val t ρ = ρ *-Var t

-- Syntactic Sugar

-- We need spine applications. The right way to formalise this is, as ever, on
-- values, and then on terms (?). To start with, we therefore need clausal
-- form for types.

-- We need a Trm-level application (to a Val), for app-cxt-sim and
-- subsequently.

-- this is Craig's version: much smoother!
val₀ : ∀ {Γ} {σ} → (σ ⊢ Val σ) Γ
val₀ {Γ} {σ} = inj var₀
 where open Morphism Var→Val ; open Model₀ 𝓥ar₀

Val→Spine : ∀ {Γ} {σ τ} (V : Val σ Γ) → Trm τ (Γ ∙ (σ `→ τ))
Val→Spine V = val₀ `$ (weak *-Var V)

appT : ∀ {Γ} {σ τ} (M : Trm (σ `→ τ) Γ) → (V : Val σ Γ) → Trm τ Γ
appT M V = `let M (Val→Spine V)

-- Val substitution

𝓥al : Model Val
𝓥al = mkModel th^Val

ext^Env : ∀ {Γ Δ Θ} {σ} → (Γ ⊨ Δ) → (Δ ⊆ Θ) → (Val σ Θ) → Γ ∙ σ ⊨ Θ
ext^Env ρ inc u = ext ρ inc u where open Thin 𝓥al

𝓥al₀ : Model₀ 𝓥al
𝓥al₀ = mkVar₀ val₀

ext₀^Env : ∀ {σ} {Γ Δ} → (Γ ⊨ Δ) → (Γ ∙ σ) ⊨ (Δ ∙ σ)
ext₀^Env = ext₀ where open Ext₀ 𝓥al₀

Val→Val : Morphism 𝓥al Val
Val→Val = ι^Inj

Substitution : Semantics Val→Val Val→Trm
Substitution = syntactic 𝓥al₀

infix 4 _*-Val_

_*-Val_ : {f : CBV} {Γ Δ : Cx} (ρ : Γ ⊨ Δ) →
          {σ : Ty} (t : Exp {f} σ Γ) → Exp {f} σ Δ
ρ *-Val e = sem ρ e where open Eval Substitution

subst : ∀ {f} {Γ Δ} {σ} → Exp {f} σ Γ → Γ ⊨ Δ → Exp {f} σ Δ
subst e ρ = ρ *-Val e

{-- Substitution lemmas; what the generic Allais machinery is for! -}

-- first one is NOT provable via generic traversal!
ext₀^Env-ext₀ : ∀ {Γ} {σ} → {ρ : Γ ⊨ Γ} → (∀ {τ} v → var ρ {τ} v ≡ `var v) →
 ∀ {τ} v → var (ext₀^Env {σ} {Γ} ρ) {τ} v ≡ `var v
ext₀^Env-ext₀ {Γ} {σ} {ρ} eq =
  [ P ][ PEq.refl ,,,  PEq.cong (weak *-Var_) ∘ eq ]
 where P = λ {τ} v → var (ext₀^Env {σ} {Γ} ρ) {τ} v ≡ `var v

ι^Env-lemma-aux : {Γ : Cx} {σ : Ty} {ρ : Γ ⊨ Γ}
             (prf : {τ : Ty} (v : Var τ Γ) → var ρ {τ} v ≡ `var v) →
             {cbv : CBV} (E : Exp {cbv} σ Γ) →
             (ρ *-Val E) ≡ E
ι^Env-lemma-aux prf  (`var v)
 rewrite prf v             = PEq.refl
ι^Env-lemma-aux prf   (`b b)    = PEq.refl
ι^Env-lemma-aux prf   (`λ M)
 rewrite ι^Env-lemma-aux (ext₀^Env-ext₀ prf) M    = PEq.refl
ι^Env-lemma-aux prf  (`val V)
 rewrite ι^Env-lemma-aux prf V  = PEq.refl
ι^Env-lemma-aux prf  (F `$ A)
 rewrite ι^Env-lemma-aux prf F | ι^Env-lemma-aux prf A = PEq.refl
ι^Env-lemma-aux prf (`if B L R)
  rewrite ι^Env-lemma-aux prf B | ι^Env-lemma-aux prf L |
          ι^Env-lemma-aux prf R = PEq.refl
ι^Env-lemma-aux prf  (`let M N)
  rewrite ι^Env-lemma-aux prf M |
          ι^Env-lemma-aux (ext₀^Env-ext₀ prf) N = PEq.refl

ι^Env-lemma : ∀ {f} {Γ} {σ} → (E : Exp {f} σ Γ) → (ι^Env *-Val E) ≡ E
ι^Env-lemma = ι^Env-lemma-aux {ρ = ι^Env} (λ v → PEq.refl)

ι^Env₀-lemma : ∀ {f} {σ} → (ρ : Env₀ ε) (E : Exp₀ {f} σ) → (ρ *-Val E) ≡ E
ι^Env₀-lemma ρ = ι^Env-lemma-aux {ρ = ρ} (λ ())

ι^Env₀ : ∀ {f} {σ} → (E : Exp₀ {f} σ) → (ι^Env {ε} *-Val E) ≡ E
ι^Env₀ = ι^Env-lemma {Γ = ε}

ext₀^Env-ext : ∀ {Γ Δ} {σ} → {ρ ρ' : Γ ⊨ Δ} →
                 (∀ {τ} v → var ρ {τ} v ≡ var ρ' v) →
 ∀ {τ} v → var (ext₀^Env {σ} {Γ} ρ) {τ} v ≡ var (ext₀^Env ρ') v
ext₀^Env-ext {Γ} {Δ} {σ} {ρ} {ρ'} eq =
  [ P ][ PEq.refl ,,,  PEq.cong (weak *-Var_) ∘ eq ]
 where P = λ {τ} v → var (ext₀^Env {σ} {Γ} ρ) {τ} v ≡ var (ext₀^Env ρ') v

-- simple instance of the fundamental Simulation lemma
subst-ext : ∀ {f} {Γ Δ} {σ} → (E : Exp {f} σ Γ) →
 {ρ ρ' : Γ ⊨ Δ} → (∀ {τ} v → var ρ {τ} v ≡ var ρ' v) → subst E ρ ≡ subst E ρ'

subst-ext (`var v) eq = eq v
subst-ext  (`b b)  eq = PEq.refl
subst-ext  (`λ M)  eq rewrite subst-ext M (ext₀^Env-ext eq) = PEq.refl
subst-ext (`val V) eq rewrite subst-ext V eq = PEq.refl
subst-ext (f `$ a) eq rewrite subst-ext f eq | subst-ext a eq = PEq.refl
subst-ext (`if b l r) eq rewrite subst-ext b eq | subst-ext l eq |
                                 subst-ext r eq = PEq.refl
subst-ext (`let M N)  eq rewrite subst-ext M eq |
                                 subst-ext N (ext₀^Env-ext eq) = PEq.refl

subst-ext₀ : ∀ {σ} → (M : Trm₀ σ) (ρ : Env₀ ε) → subst M ρ ≡ subst M ι^Env
subst-ext₀ M ρ = subst-ext M {ρ = ρ} {ρ' = ι^Env {ε}} (λ ())

-- composition of valuations: sub-sub fusion
_*-Sub_ : ∀ {Γ Δ Ξ} → (ρ : Δ ⊨ Ξ) → (ρ' : Γ ⊨ Δ) → Γ ⊨ Ξ
ρ *-Sub ρ' = map-Env (ρ *-Val_) ρ'

lemma33 : ∀ {f} {Γ Δ Ξ} {σ} → (ρ : Δ ⊨ Ξ) → (ρ' : Γ ⊨ Δ) → (E : Exp {f} σ Γ) →
 ((ρ *-Sub ρ') *-Val E) ≡ (ρ *-Val (ρ' *-Val E))
lemma33 ρ ρ' (`var v) = PEq.refl
lemma33 ρ ρ' (`b b)  = PEq.refl
lemma33 ρ ρ' (`λ M)  = PEq.cong λλ (lemma33 (ext₀^Env ρ) (ext₀^Env ρ') M)
lemma33 ρ ρ' (`val V) rewrite lemma33 ρ ρ' V = PEq.refl
lemma33 ρ ρ'   (f `$ a) rewrite lemma33 ρ ρ' f | lemma33 ρ ρ' a = PEq.refl
lemma33 ρ ρ' (`if b l r) rewrite lemma33 ρ ρ' b | lemma33 ρ ρ' l |
                                 lemma33 ρ ρ' r = PEq.refl
lemma33 ρ ρ'  (`let M N) rewrite lemma33 ρ ρ' M =
  PEq.cong (`let _) (lemma33 (ext₀^Env ρ) (ext₀^Env ρ') N)

infixl 10 _⟨_/var₀⟩

_⟨_/var₀⟩ : ∀ {f} {σ τ} → [ σ ⊢ Exp {f} τ ⟶ Val σ ⟶ Exp {f} τ ]
E ⟨ U /var₀⟩ = subst E (ι^Env `∙ U)

lemma34 : ∀ {f} {Γ Δ} {σ τ} → (E : (σ ⊢ Exp {f} τ) Γ) → (ρ : Γ ⊨ Δ) → ∀ U →
 subst E (ρ `∙ U) ≡ subst E (ext₀^Env ρ) ⟨ U /var₀⟩
lemma34 E ρ U = lemma33 (ι^Env `∙ U) (ext₀^Env ρ) E
