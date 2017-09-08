module relations where

open import Level as L using (Level ; _⊔_)
open import Data.Bool renaming (true to tt ; false to ff)
open import Data.Product hiding (map)
open import Function as F hiding (_∋_ ; _$_)
open import Relation.Binary.PropositionalEquality as PEq using (_≡_)

open import lambda-fg
open import acmm
open import sim-fusion-lemmas

{---------------}
{-- Relations --}
{---------------}

Rel^E : {f : CBV} {ℓ : Level} {Γ : Cx} {τ : Ty} → Set (L.suc ℓ)
Rel^E {f} {ℓ} {Γ} {τ} = (M N : Exp {f} τ Γ) → Set ℓ

Rel^T : {ℓ : Level} {Γ : Cx} {τ : Ty} → Set (L.suc ℓ)
Rel^T {ℓ} {Γ} {τ} = Rel^E {`trm }{ℓ} {Γ} {τ}

Rel^S : {ℓ : Level} {σ τ : Ty} → Set (L.suc ℓ)
Rel^S {ℓ} {σ} {τ} = (S^M S^N : Frm σ τ) → Set ℓ

Rel^V : {ℓ : Level} {Γ : Cx} {τ : Ty} → Set (L.suc ℓ)
Rel^V {ℓ} {Γ} {τ} = Rel^E {`val} {ℓ} {Γ} {τ}

Rel^B : {ℓ : Level} {Γ : Cx} {β : BTy} → Set (L.suc ℓ)
Rel^B {ℓ} {Γ} {β} = (M N : ⟦ β ⟧B) → Set ℓ -- Rel^V {ℓ} {Γ} {`b β} --

-- Val restriction of a Trm-level relation

infix 5 _[_]^V_

_[_]^V_ : {ℓ^T : Level} {Γ : Cx} {τ : Ty}
         (V : Val τ Γ) (R : Rel^T {ℓ^T} {Γ} {τ}) (W : Val τ Γ) → Set ℓ^T

V [ R ]^V W = R (`val V) (`val W)

-- BTy restriction of a Val-level relation

infix 5 _[_]^B_ -- not currently exploited

_[_]^B_ : {ℓ^T : Level} {Γ : Cx} {β : BTy}
         (V : ⟦ β ⟧B) (R : Rel^V {ℓ^T} {Γ} {`b β}) (W : ⟦ β ⟧B) → Set ℓ^T

V [ R ]^B W = R (`b V) (`b W)

GRel^E : {f : CBV} {ℓ : Level} {τ : Ty} → Set (L.suc ℓ)
GRel^E {f} {ℓ} {τ} = Rel^E {f} {ℓ} {ε} {τ}

GRel^B : {ℓ : Level} {β : BTy} → Set _
GRel^B {ℓ} {β} = Rel^B {ℓ} {ε} {β}

GRel^V : {ℓ : Level} {τ : Ty} → Set _
GRel^V {ℓ} {τ} = Rel^V {ℓ} {ε} {τ}

GRel^T : {ℓ : Level} {τ : Ty} → Set _
GRel^T {ℓ} {τ} = Rel^T {ℓ} {ε} {τ}

-- unary open extension of a Trm-level relation:
-- from arbitrary Γ to ε via closing substitution ρ : Env₀ Γ
infix 5 _[_]^O_

_[_]^O_ : {ℓ : Level} {Γ : Cx} {τ : Ty}
         (M : Trm τ Γ) (R : GRel^T {ℓ} {τ}) (N : Trm τ Γ) → Set ℓ

M [ R ]^O N = (ρ : Env₀ _) → R (ρ *-Val M) (ρ *-Val N)

GRel₀^E : Set _
GRel₀^E = ∀ {f} {τ} → GRel^E {f} {L.zero} {τ}

GRel₀^B : Set _
GRel₀^B = ∀ {τ} → GRel^B {L.zero} {τ}

GRel₀^V : Set _
GRel₀^V = ∀ {τ} → GRel^V {L.zero} {τ}

GRel₀^T : Set _
GRel₀^T = ∀ {τ} → GRel^T {L.zero} {τ}

infixr 10 _[_]^Env_
_[_]^Env_ : ∀ {ℓ} {Γ Δ} (ρ^L : Γ ⊨ Δ)
            (𝓔^R : ∀ {τ} → Rel^V {ℓ} {Δ} {τ}) (ρ^R : Γ ⊨ Δ) → Set ℓ
ρ^L [ 𝓔^R ]^Env ρ^R = ∀ {σ} v → 𝓔^R {σ} (var ρ^L v) (var ρ^R v)

[_]^Env-refl : ∀ {ℓ} {Γ Δ} {𝓔^R : ∀ {τ} → Rel^V {ℓ} {Δ} {τ}} →
 (r : ∀ {σ} V → 𝓔^R {σ} V V) → (ρ : Γ ⊨ Δ) → ρ [ 𝓔^R ]^Env ρ
[ r ]^Env-refl ρ    = r ∘ (var ρ)

[_]^Env-refl₀ : ∀ {ℓ} {Δ} (𝓔^R : ∀ {τ} → Rel^V {ℓ} {Δ} {τ}) →
 (ρ : ε ⊨ Δ) → ρ [ 𝓔^R ]^Env ρ
[ 𝓔^R ]^Env-refl₀ ρ ()

infixl 10 _∙₀^R_
_∙₀^R_ :  ∀ {ℓ} {Γ} {𝓔^R : ∀ {τ} → GRel^V {ℓ} {τ}}
            {ρ^L ρ^R : Env₀ Γ} {σ} {u^L} {u^R} →
 ρ^L [ 𝓔^R ]^Env ρ^R → 𝓔^R {σ} u^L u^R → (ρ^L `∙ u^L) [ 𝓔^R ]^Env (ρ^R `∙ u^R)
(env^R ∙₀^R val^R)   ze   = val^R
(env^R ∙₀^R val^R) (su v) = env^R v

Val₀→Env₀ : ∀ {ℓ} {𝓔^R : ∀ {τ} → GRel^V {ℓ} {τ}} {σ} {u^L} {u^R} →
 𝓔^R {σ} u^L u^R → (`ε {Γ = ε} `∙ u^L) [ 𝓔^R ]^Env (`ε {Γ = ε} `∙ u^R)
Val₀→Env₀ {ℓ} {𝓔^R} rel = _∙₀^R_ {𝓔^R = 𝓔^R} (λ ()) rel

-- binary open extension of a Exp-level relation:
-- from arbitrary Γ to ε via related closing substitutions ρ ρ' : Env₀ Γ
infix 5 _O^[_]^O_

_O^[_]^O_ : ∀ {ℓ} {f} {Γ} {τ}
         (M : Exp {f} τ Γ)
         (R : ∀ {f} {τ} → GRel^E {f} {ℓ} {τ}) (N : Exp {f} τ Γ) → Set ℓ

M O^[ R ]^O N = {ρ ρ' : Env₀ _} → ρ [ R {`val} ]^Env ρ' →
  R (ρ *-Val M) (ρ' *-Val N)

-- Big-step Evaluation

data _⇓_ : {τ : Ty} (M : Trm₀ τ) (V : Val₀ τ) → Set where

  ⇓val   : {τ : Ty} {V : Val₀ τ} →
           (`val V) ⇓ V

  ⇓if-tt : {τ : Ty} {M N : Trm₀ τ} {V : Val₀ τ} → M ⇓ V →
           (`if (`b tt) M N) ⇓ V

  ⇓if-ff : {τ : Ty} {M N : Trm₀ τ} {V : Val₀ τ} → N ⇓ V →
           (`if (`b ff) M N) ⇓ V

  ⇓app   : {σ τ : Ty} {M : (σ ⊢ Trm τ) _} {V : _} {U : _} →
           (M ⟨ V /var₀⟩) ⇓ U → (βV M V) ⇓ U

  ⇓let   : {σ τ : Ty} {M : _} {N : (σ ⊢ Trm τ) _} {V : _} {U : _} →
           M ⇓ V → (N ⟨ V /var₀⟩) ⇓ U → (`let M N) ⇓ U

-- One-step reduction

data _→₁_ : GRel₀^T where

  →₁if    : {τ : Ty} {M N : Trm₀ τ} {b : Bool} →
            (`if (`b b) M N) →₁ (if b then M else N)

  →₁app   : {σ τ : Ty} {M : (σ ⊢ Trm τ) _} {V : _} →
            (βV M V) →₁ (M ⟨ V /var₀⟩)
{-
Slight deviation from the paper. The rules below are not defined inductively
as relation => but instead are shown to be admissible (see big-step-prop.agda)

  →₁letV  : {σ τ : Ty} {N : (σ ⊢ Trm τ) _} {V : _} →
            (letV V N) →₁ (N ⟨ V /var₀⟩T)

  →₁letT  : {σ τ : Ty} {N : (σ ⊢ Trm τ) _} {M M' : _} →
            M →₁ M' → (`let M N) →₁ (`let M' N)
-}

-- a fundamental relation transformer: lifting relations on Val to relations
-- on Trm

infix 5 _[_]^T_

_[_]^T_ : {ℓ^V : Level} {τ : Ty}
         (M : Trm₀ τ) (R : GRel^V {ℓ^V} {τ}) (N : Trm₀ τ) → Set ℓ^V

M [ R ]^T N = ∀ {U} → M ⇓ U → ∃ λ V → N ⇓ V × R U V

V^[_]^T^V : {ℓ^V : Level} {τ : Ty} {R : GRel^V {ℓ^V} {τ}}
  {V W : Val₀ τ} → R V W → V [ _[ R ]^T_ ]^V W -- (`val V) [ R ]^T  (`val W)
V^[ r ]^T^V ⇓val = _ , ⇓val , r

T^V^[_]^V : {ℓ^V : Level} {τ : Ty} {R : GRel^V {ℓ^V} {τ}}
  {V W : Val₀ τ} → V [ _[ R ]^T_ ]^V W → R V W -- (`val V) [ R ]^T  (`val W)
T^V^[ r ]^V with r ⇓val
... | _ , ⇓val , rVW = rVW

-- Frame stack evaluation

data _,_↓_ : {σ τ : Ty} (S : Frm τ σ) (M : Trm₀ σ) (V : Val₀ τ) → Set where

  ↓val    : ∀ {τ} {V : Val₀ τ} →
           Id , `val V ↓ V

  ↓red   : ∀ {σ τ} {S : Frm τ σ} {M N} {U} →
           M →₁ N → S , N ↓ U → S , M ↓ U

  ↓letV  : ∀ {σ τ υ} {S : Frm υ τ} {N : (σ ⊢ Trm τ) _} {V} {U} →
           S , N ⟨ V /var₀⟩ ↓ U → (S ∙ N) , `val V ↓ U

  ↓letT  : ∀ {σ τ υ} {S : Frm υ τ} {M} {N : (σ ⊢ Trm τ) _} {U} →
           (S ∙ N) , M ↓ U → S , `let M N ↓ U

-- fundamental relation transformers: lifting relations on Val/Trm to
-- relations on <Frm, Trm> configurations

infix 5 _,_[_]^F_,_
infix 5 _[_&_]^F_

_,_[_]^F_,_ : {ℓ^V : Level} {σ τ : Ty}
         (S : Frm σ τ) (M : Trm₀ τ) (R : GRel^V {ℓ^V} {σ}) (T : Frm σ τ)
         (N : Trm₀ τ) → Set ℓ^V
S , M [ R ]^F T , N = ∀ {U} → S , M ↓ U → ∃ λ V → T , N ↓ V × R U V

_[_&_]^F_ : {ℓ : Level} {σ τ : Ty}
         (M : Trm₀ τ) (R^S : Rel^S {ℓ} {σ} {τ}) (R^V : GRel^V {ℓ} {σ})
         (N : Trm₀ τ) → Set ℓ
M [ R^S & R^V ]^F N = ∀ {S T} → R^S S T → S , M [ R^V ]^F T , N
