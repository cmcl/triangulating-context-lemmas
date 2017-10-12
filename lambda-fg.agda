{-- Fine-grained call-by-value lambda calculus -}
{-# OPTIONS --copatterns #-}
module lambda-fg where

open import Level as L using (Level ; _⊔_)
open import Data.Empty
open import Data.Unit renaming (tt to ⟨⟩)
open import Data.Bool renaming (true to tt ; false to ff)
open import Data.Sum hiding (map ; [_,_])
open import Data.Product hiding (map)
open import Function as F hiding (_∋_ ; _$_)

open import Data.Nat as ℕ using (ℕ ; _+_)

open import Relation.Binary.PropositionalEquality as PEq using (_≡_)

infixr 20 _`→_
infixl 10 _∙_

-- Base types and their interpretations, types, and contexts.

data BTy : Set where
  `U : BTy
  `B : BTy
  `N : BTy

⟦_⟧B : BTy → Set
⟦ `U ⟧B = ⊤
⟦ `B ⟧B = Bool
⟦ `N ⟧B = ℕ

data Ty : Set where
  `b   : (β : BTy) → Ty
  _`→_ : (σ τ : Ty) → Ty

data Cx : Set where
  ε    : Cx
  _∙_  : Cx → Ty → Cx

-- Generic operations on Cx-indexed families

infixr 5 _⟶_

_⇒_ : {ℓ^A ℓ^E : Level} →
      (Cx → Set ℓ^A) → (Cx → Set ℓ^E) → (Cx → Cx → Set (ℓ^A ⊔ ℓ^E))
(S ⇒ T) Γ Δ = S Γ → T Δ

_⟶_ : {ℓ^A ℓ^E : Level} →
       (Cx → Set ℓ^A) → (Cx → Set ℓ^E) → (Cx → Set (ℓ^A ⊔ ℓ^E))
(S ⟶ T) Γ = (S ⇒ T) Γ Γ

[_] : {ℓ^A : Level} → (Cx → Set ℓ^A) → Set ℓ^A
[ T ] = ∀ {Γ} → T Γ

-- Syntax for extending a Cx-indexed family by a single Ty
_⊢_ : {ℓ^A : Level} → Ty → (Cx → Set ℓ^A) → (Cx → Set ℓ^A)
(σ ⊢ S) Γ = S (Γ ∙ σ)

infixr 6 _⊢_

-- Type- and Scope-safe variable bindings, 
-- as dependently-typed de Bruijn indices

data Var (τ : Ty) : Cx → Set where
  ze  :            -- ∀ Γ. Var τ (Γ ∙ τ)
                   [          τ ⊢ Var τ ]
  su  :            -- ∀ Γ σ. Var τ Γ → Var τ (Γ ∙ σ)
       {σ : Ty} →  [ Var τ ⟶  σ ⊢ Var τ ]

-- A useful helper function for lemmas about variable manipulations.
infix 5 [_][_,,,_]
[_][_,,,_] : {ℓ : Level} {Γ : Cx} {σ : Ty} (P : {τ : Ty}
             (v : Var τ (Γ ∙ σ)) → Set ℓ) → (pZ : P ze) →
             (pS : {τ : Ty} (n : Var τ Γ) → P (su n)) →
             {τ : Ty} (v : Var τ (Γ ∙ σ)) → P {τ} v
[ P ][ pZ ,,, pS ] ze     = pZ
[ P ][ pZ ,,, pS ] (su n) = pS n

-- Judgments-as-types (sic)
-- The type of the grammar in lambda-fg.

PreModel : (ℓ : Level) → Set (L.suc ℓ)
PreModel ℓ = Ty → Cx → Set ℓ

PreMorphism : {ℓ^E ℓ^F : Level}
              (𝓔 : PreModel ℓ^E) (𝓕 : PreModel ℓ^F) → Set (ℓ^E ⊔ ℓ^F)
PreMorphism 𝓔 𝓕 = ∀ {σ} → [ 𝓔 σ ⟶ 𝓕 σ ]

infixl 5 _`$_

data CBV : Set
 where `val `trm : CBV

module Admits {ℓ : Level} (𝓔 : {f : CBV} → PreModel ℓ)
 where

-- value constructors
  admits-b : Set ℓ
  admits-b = {β : BTy} → (b : ⟦ β ⟧B) → [ 𝓔 {`val} (`b β) ]

  admits-λ : Set ℓ
  admits-λ = {σ τ : Ty} → [ σ ⊢ 𝓔 {`trm} τ ⟶ 𝓔 {`val} (σ `→ τ) ]

-- term constructors
  admits-$ : Set ℓ
  admits-$ = {σ τ : Ty} → [ 𝓔 {`val} (σ `→ τ) ⟶ 𝓔 {`val} σ  ⟶ 𝓔 {`trm} τ ]

  admits-if : Set ℓ
  admits-if =
    {σ : Ty} → [ 𝓔 {`val} (`b `B)  ⟶ 𝓔 {`trm} σ ⟶ 𝓔 {`trm} σ ⟶ 𝓔 {`trm} σ ]

  admits-let : Set ℓ
  admits-let = {σ τ : Ty} → [ 𝓔 {`trm} σ  ⟶ σ ⊢ 𝓔 {`trm} τ ⟶ 𝓔 {`trm} τ ]

open Admits public

-- Fine-grained CBV, with explicit var and val constructors.
mutual

 Val : PreModel L.zero
 Val = Exp {`val}

 Trm : PreModel L.zero
 Trm = Exp {`trm}

 data Exp : {f : CBV} → PreModel L.zero where

  `var    : PreMorphism Var Val
    -- {σ : Ty}   → [ Var σ ⟶                Val σ ]

  `b      : admits-b   λ {f} → Exp {f}
    -- {β : BTy}  → (b : ⟦ β ⟧B) →      [ Val (`b β) ]

  `λ      : admits-λ   λ {f} → Exp {f}
    -- {σ τ : Ty} → [  σ ⊢ Trm τ   ⟶  Val (σ `→ τ) ]

  `val    : PreMorphism Val Trm
    -- {σ : Ty}   → [ Val σ ⟶                Trm σ ]

  _`$_    : admits-$   λ {f} → Exp {f}
    -- {σ τ : Ty} → [ Val (σ `→ τ) ⟶  Val σ  ⟶ Trm τ ]

  `if     : admits-if  λ {f} → Exp {f}
    -- {σ : Ty} → [ Val (`b `B) ⟶ Trm σ ⟶ Trm σ ⟶ Trm σ ]

  `let    : admits-let λ {f} → Exp {f}
    -- {σ τ : Ty} → [ Trm σ ⟶ σ ⊢ Trm τ ⟶ Trm τ ]

-- Injection of values into terms
Val→Trm : PreMorphism Exp Exp -- Val Trm
Val→Trm = `val

-- (ground) instances

Exp₀ : ∀ {f} τ → Set
Exp₀ {f} τ = Exp {f} τ ε

Val₀ : ∀ τ → Set
Val₀ = Exp₀ {`val}

Trm₀ : ∀ τ → Set
Trm₀ = Exp₀ {`trm}

-- dumb constructor, fixing types for overloaded constructor names in PEq.cong
-- proofs (grr!)

λλ  : {σ τ : Ty} → [ σ ⊢ Trm τ ⟶ Val (σ `→ τ) ]
λλ  = `λ

-- smart constructors, selecting correct Exp instances

βV : ∀ {σ τ} → [ σ ⊢ Exp τ ⟶  Exp σ ⟶ Exp τ ]
βV M U = (`λ M) `$ U

letV : ∀ {σ τ} → [ Exp σ ⟶ σ ⊢ Exp τ ⟶ Exp τ ]
letV V M = `let (`val V) M

`λ-inj : ∀ {Γ} {σ τ} {M N : Trm τ (Γ ∙ σ)}
 (eq : (Val (σ `→ τ) Γ F.∋ `λ M) ≡ `λ N) → M ≡ N
`λ-inj PEq.refl = PEq.refl

-- Environments

infix 5 _-Env

record _-Env {ℓ : Level} (Γ : Cx) (𝓥 : PreModel ℓ) (Δ : Cx) : Set ℓ
 where
  constructor mkEnv; field var : {σ : Ty} → Var σ Γ → 𝓥 σ Δ

infix 6 _⊆_
infixr 6 _⊨_

-- renamings: arbitrary weakenings and permutations

_⊆_ : (Γ Δ : Cx) → Set
Γ ⊆ Δ = (Γ -Env) Var Δ

-- Value substitutions

_⊨_ : (Γ Δ : Cx) → Set
Γ ⊨ Δ = (Γ -Env) Val Δ --  ⊨ is fatter than ⊧, \models;  ⊨ is '\ | ='

Env₀ : ∀ Γ → Set
Env₀ Γ = Γ ⊨ ε

open _-Env public

ι^Var : ∀ {Γ} → (Γ -Env) Var Γ
var ι^Var = id

ι^Env : ∀ {Γ} → Γ ⊨ Γ
var ι^Env = `var

ι^Exp : ∀ {Γ} → (Γ -Env) Trm Γ
var ι^Exp v = `val (`var v)

map-Env : {ℓ^A ℓ^B : Level} {𝓥 : PreModel ℓ^A} {𝓦 : PreModel ℓ^B} {Γ Δ Θ : Cx}
          (f : {σ : Ty} → 𝓥 σ Δ → 𝓦 σ Θ) → (Γ -Env) 𝓥 Δ → (Γ -Env) 𝓦 Θ
var (map-Env f ρ) = f ∘ (var ρ)

refl^Var : ∀ {Γ} → Γ ⊆ Γ
refl^Var = ι^Var

weak : ∀ {Γ}{σ} → Γ ⊆ (Γ ∙ σ)
var weak = su

infix 4 _*-Env_

_*-Env_ : {ℓ : Level} {𝓥 : PreModel ℓ} {Γ Δ : Cx} →
          Γ ⊆ Δ → [ (Δ -Env) 𝓥  ⟶  (Γ -Env) 𝓥 ]
var (inc *-Env ρ) = var ρ ∘ var inc

trans^Var : ∀ {Γ Δ Θ} (inc₁ : Γ ⊆ Δ) (inc₂ : Δ ⊆ Θ) → Γ ⊆ Θ
trans^Var inc = inc *-Env_

_-⟦_⟧  : {ℓ : Level} → Cx → CBV → (𝓒 : {f : CBV} → PreModel ℓ) → Cx → Set ℓ
(Γ -⟦ f ⟧) 𝓒 Δ = {σ : Ty} → Exp {f} σ Γ → 𝓒 {f} σ Δ

infixl 10 _`∙_

`ε   : {ℓ : Level} {𝓥 : PreModel ℓ} → [ (ε -Env) 𝓥 ]
_`∙_ : {ℓ : Level} {Γ : Cx} {𝓥 : PreModel ℓ} {σ : Ty} →
       [ (Γ -Env) 𝓥 ⟶ 𝓥 σ ⟶ (Γ ∙ σ -Env) 𝓥 ]

var `ε        ()
var (ρ `∙ s)  ze      = s
var (ρ `∙ s)  (su n)  = var ρ n

-- The fundamental Kripke co-monad structure on Premodels.

□ : {ℓ : Level} → (Cx → Set ℓ) → (Cx → Set ℓ)
(□ S) Γ = {Δ : Cx} → Γ ⊆ Δ → S Δ

Thinnable : {ℓ : Level} → (Cx → Set ℓ) → Set ℓ
Thinnable S = [ S ⟶ (□ S) ] -- {Γ Δ : Cx} → S Γ → Γ ⊆ Δ → S Δ

-- Syntactic categories are Premodels closed under thinning.

record Model {ℓ : Level} (𝓥 : PreModel ℓ) : Set ℓ where
  constructor mkModel; field thin : {σ : Ty} → Thinnable (𝓥 σ)

-- In particular, variables are closed under thinning.

th^Var : {σ : Ty} → Thinnable (Var σ)
th^Var v inc = var inc v

𝓥ar : Model Var
𝓥ar = mkModel th^Var

record Morphism {ℓ^V ℓ^T : Level}
 {𝓥 : PreModel ℓ^V} (Θ : Model 𝓥) (𝓣 : PreModel ℓ^T) : Set (ℓ^V ⊔ ℓ^T)
 where
  constructor mkMorphism
  field inj : PreMorphism 𝓥 𝓣

ι^Inj : {ℓ : Level} {𝓥 : PreModel ℓ} {Θ : Model 𝓥} → Morphism Θ 𝓥
ι^Inj = mkMorphism id

Var→Val : Morphism 𝓥ar Val
Var→Val = mkMorphism `var

-- structure of Thinnables

module Thin {ℓ : Level} {𝓒 : PreModel ℓ} (Θ : Model 𝓒) where

 open Model Θ

 th^⇒[_] : {ℓ : Level} (𝓔 : PreModel ℓ) →
           {σ : Ty} → {Γ : Cx} → Thinnable (((𝓔 σ) ⇒ (𝓒 σ)) Γ)
 th^⇒[ 𝓔 ] {σ} ρ inc e = thin {σ} (ρ e) inc

 th : {Γ : Cx} → Thinnable ((Γ -Env) 𝓒)
 var (th ρ inc) = th^⇒[ Var ] (var ρ) inc

 ext : {Γ : Cx} {σ : Ty} → [ ((Γ -Env) 𝓒) ⟶  □ ((𝓒 σ) ⟶ ((Γ ∙ σ) -Env) 𝓒) ]
 ext ρ inc u = th ρ inc `∙ u

ext^Var : ∀ {Γ Δ Θ} {σ} → (Γ ⊆ Δ) → (Δ ⊆ Θ) → (Var σ Θ) → (Γ ∙ σ) ⊆ Θ
ext^Var ρ inc u = ext ρ inc u where open Thin 𝓥ar

-- having a notion of distinguished element under context extension

record Model₀ {ℓ^V : Level} {𝓥 : PreModel ℓ^V} (Θ : Model 𝓥) : Set (ℓ^V)
 where
  constructor mkVar₀
  field  var₀  : {σ : Ty} → [ σ ⊢ 𝓥 σ ]

𝓥ar₀ : Model₀ 𝓥ar
𝓥ar₀ = mkVar₀ ze

val₀ : ∀ {Γ} {σ} → (σ ⊢ Val σ) Γ
val₀ {Γ} {σ} = inj var₀
 where open Morphism Var→Val ; open Model₀ 𝓥ar₀

module Ext₀ {ℓ^V : Level} {𝓥 : PreModel ℓ^V} {Θ : Model 𝓥} (mod : Model₀ Θ)
 where
  open Thin Θ
  open Model₀ mod

  ext₀ : {σ : Ty} {Γ Δ : Cx} → ((Γ -Env) 𝓥 Δ) → (((Γ ∙ σ) -Env) 𝓥 (Δ ∙ σ))
  ext₀ ρ = ext ρ weak var₀

ext₀^Var : {σ : Ty} {Γ Δ : Cx} → Γ ⊆ Δ → (Γ ∙ σ) ⊆ (Δ ∙ σ)
ext₀^Var = ext₀ where open Ext₀ 𝓥ar₀

-- Framestacks

data Frm : Ty → (Ty → Set) where

 Id   : ∀ {τ}                                       → Frm τ τ
 _∙_  : ∀ {υ τ σ} (S : Frm υ τ) (N : (σ ⊢ Trm τ) ε) → Frm υ σ

-- Left action (@) over frame stacks.

letF : ∀ {τ σ} (S : Frm τ σ) (M : Trm₀ σ) → Trm₀ τ
letF   Id    M = M
letF (S ∙ N) M = letF S (`let M N)
