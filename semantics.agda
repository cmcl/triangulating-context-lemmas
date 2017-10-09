module semantics where

open import Level as L using (Level ; _⊔_)

open import lambda-fg

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
