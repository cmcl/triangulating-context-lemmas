module simulation where

open import Level as L using (Level ; _⊔_)
open import Function as F hiding (_∋_ ; _$_)

open import lambda-fg
open import acmm

-- A relational premodel
record RPreModel {ℓ^A ℓ^B : Level} (𝓔^A : PreModel ℓ^A) (𝓔^B : PreModel ℓ^B)
        (ℓ^R : Level) : Set (ℓ^A ⊔ ℓ^B ⊔ L.suc ℓ^R) where
  constructor mkRPreModel
  field rmodel : {σ : Ty} → [ 𝓔^A σ ⟶ 𝓔^B σ ⟶ const (Set ℓ^R) ]
open RPreModel public

-- The pointwise lifting of a relational premodel to contexts.
record `∀[_] {ℓ^A ℓ^B ℓ^R : Level}
      {𝓔^A : PreModel ℓ^A} {𝓔^B : PreModel ℓ^B} (𝓔^R : RPreModel 𝓔^A 𝓔^B ℓ^R)
      {Γ Δ : Cx} (ρ^A : (Γ -Env) 𝓔^A Δ) (ρ^B : (Γ -Env) 𝓔^B Δ) : Set ℓ^R where
  constructor env^R
  field var^R : {σ : Ty} (v : Var σ Γ) →
                   rmodel 𝓔^R {σ} {Δ} (var ρ^A v) (var ρ^B v)
open `∀[_] -- public

-- Related enviornments can be extended with related elements.
infixl 10 _∙^R_
_∙^R_ :  ∀ {ℓ^A ℓ^B ℓ^R : Level}
    {𝓔^A : PreModel ℓ^A} {𝓔^B : PreModel ℓ^B} {𝓔^R : RPreModel 𝓔^A 𝓔^B ℓ^R}
    {Δ Γ} {ρ^A : (Γ -Env) 𝓔^A Δ} {ρ^B} {σ} {u^A : 𝓔^A σ Δ} {u^B} →
 `∀[ 𝓔^R ] ρ^A ρ^B → rmodel 𝓔^R u^A u^B → `∀[ 𝓔^R ] (ρ^A `∙ u^A) (ρ^B `∙ u^B)
var^R (ρ^R ∙^R u^R)   ze   = u^R
var^R (ρ^R ∙^R u^R) (su v) = var^R ρ^R v

-- A relational model is a relational premodel whose related environments can
-- be thinned (and are still related).
record RModel {ℓ^A ℓ^B ℓ^R : Level}
              {𝓥^A : PreModel ℓ^A} {Θ^A : Model 𝓥^A}
              {𝓥^B : PreModel ℓ^B} {Θ^B : Model 𝓥^B}
              (𝓥^R : RPreModel 𝓥^A 𝓥^B ℓ^R) : Set (ℓ^A ⊔ ℓ^B ⊔ L.suc ℓ^R)
 where

  constructor mkRModel

  th^A = Thin.th Θ^A
  th^B = Thin.th Θ^B

  field

   th^R : ∀ {Γ Δ} → {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : (Γ -Env) 𝓥^B Δ} →
             `∀[ 𝓥^R ] ρ^A ρ^B → {Θ : Cx} (inc : Δ ⊆ Θ) →
             `∀[ 𝓥^R ] (th^A ρ^A inc) (th^B ρ^B inc)

-- Related values that inject into terms map to related terms.
RPreMorphism : {ℓ^A ℓ^M ℓ^B ℓ^N ℓ^RV ℓ^RT : Level}
 {𝓥^A : PreModel ℓ^A} {𝓣^A : PreModel ℓ^M}
 {𝓥^B : PreModel ℓ^B} {𝓣^B : PreModel ℓ^N}
 (𝓥^R : RPreModel 𝓥^A 𝓥^B ℓ^RV)
 (inj^A : PreMorphism 𝓥^A 𝓣^A) (inj^B : PreMorphism 𝓥^B 𝓣^B)
 (𝓣^R  : RPreModel 𝓣^A 𝓣^B ℓ^RT) → Set (ℓ^RV ⊔ ℓ^RT ⊔ ℓ^A ⊔ ℓ^B)
RPreMorphism 𝓥^R inj^A inj^B 𝓣^R =
 ∀ {Γ} {σ} {a} {b} → rmodel 𝓥^R {σ} {Γ} a b → rmodel 𝓣^R (inj^A a) (inj^B b)

-- TODO: Enforce the value relational premodel to be a model?
record RMorphism {ℓ^A ℓ^M ℓ^B ℓ^N ℓ^RV ℓ^RT : Level}
   {𝓥^A : PreModel ℓ^A} {Θ^A : Model 𝓥^A}
   {𝓣^A : PreModel ℓ^M}
   {𝓥^B : PreModel ℓ^B} {Θ^B : Model 𝓥^B}
   {𝓣^B : PreModel ℓ^N}
   {𝓥^R  : RPreModel 𝓥^A 𝓥^B ℓ^RV}
   -- (Θ^R : RModel {Θ^A = Θ^A} {Θ^B = Θ^B} 𝓥^R)
   (𝓘^A : Morphism Θ^A 𝓣^A) (𝓘^B : Morphism Θ^B 𝓣^B)
   (𝓣^R  : RPreModel 𝓣^A 𝓣^B ℓ^RT) : Set (ℓ^RV ⊔ ℓ^RT ⊔ ℓ^A ⊔ ℓ^B ⊔ ℓ^M ⊔ ℓ^N)
 where

 constructor mkRInj

 inj^A = Morphism.inj 𝓘^A
 inj^B = Morphism.inj 𝓘^B

 field
   R⟦inj⟧ : RPreMorphism 𝓥^R inj^A inj^B 𝓣^R

record Simulation {ℓ^A ℓ^M ℓ^B ℓ^N ℓ^RV ℓ^RT : Level}
 {𝓥^A : PreModel ℓ^A} {Θ^A : Model 𝓥^A} {𝓔^A : {f : CBV} → PreModel ℓ^M}
 {𝓥^B : PreModel ℓ^B} {Θ^B : Model 𝓥^B} {𝓔^B : {f : CBV} → PreModel ℓ^N}
 {var^A : Morphism Θ^A (𝓔^A {`val})} -- injection of variables into
                                         -- values.
 {val^A : PreMorphism (𝓔^A {`val}) (𝓔^A {`trm})} -- values to term
                                                         -- injection.
 -- Analogous maps for 𝓔^B.
 {var^B : Morphism Θ^B (𝓔^B {`val})}
 {val^B : PreMorphism (𝓔^B {`val}) (𝓔^B {`trm})}

 (𝓢^A : Semantics {Θ = Θ^A} {𝓔 = λ {f} → 𝓔^A {f}} var^A val^A)
 (𝓢^B : Semantics {Θ = Θ^B} {𝓔 = λ {f} → 𝓔^B {f}} var^B val^B)

 {𝓥^R : RPreModel 𝓥^A 𝓥^B ℓ^RV} {Θ^R : RModel {Θ^A = Θ^A} {Θ^B = Θ^B} 𝓥^R}

 {𝓔^R : {f : CBV} → RPreModel (𝓔^A {f}) (𝓔^B {f}) ℓ^RT}

 (var^R : RMorphism {𝓥^R = 𝓥^R} var^A var^B (𝓔^R {`val}))
 (val^R : RPreMorphism (𝓔^R {`val}) val^A val^B (𝓔^R {`trm}))

 : Set (ℓ^RV ⊔ ℓ^A ⊔ ℓ^B ⊔ ℓ^M ⊔ ℓ^N ⊔ ℓ^RT)
 where
  th^A  = Thin.th Θ^A
  th^B  = Thin.th Θ^B
  ext^A  = Thin.ext Θ^A
  ext^B  = Thin.ext Θ^B
  sem^A  = Eval.sem 𝓢^A
  sem^B  = Eval.sem 𝓢^B

  𝓡 : ∀ {f} {Γ Δ} {σ} →
      Exp {f} σ Γ → (Γ -Env) 𝓥^A Δ → (Γ -Env) 𝓥^B Δ → Set (ℓ^RT)
  𝓡 {f} E ρ^A ρ^B = rmodel (𝓔^R {f}) (sem^A {f} ρ^A E) (sem^B {f} ρ^B E)

  field
    R⟦b⟧  :  ∀ {Γ Δ} {β} → (b : ⟦ β ⟧B) →
             {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : (Γ -Env) 𝓥^B Δ} →
             `∀[ 𝓥^R ] ρ^A ρ^B → 𝓡 (`b b) ρ^A ρ^B

    R⟦λ⟧ :  ∀ {Γ Δ} {σ τ} {M : Trm τ (Γ ∙ σ)}
            {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : (Γ -Env) 𝓥^B Δ}
            (r : ∀ {Θ} {u^A : 𝓥^A σ Θ} {u^B : 𝓥^B σ Θ} →
               ∀ inc → rmodel 𝓥^R u^A u^B →
                 let  ρ^A′ = ext^A ρ^A inc u^A
                      ρ^B′ = ext^B ρ^B inc u^B
                 in 𝓡 M ρ^A′ ρ^B′) →
            `∀[ 𝓥^R ] ρ^A ρ^B → 𝓡 (`λ M) ρ^A ρ^B

    R⟦$⟧  :  ∀ {Γ Δ} {σ τ} {f : Val (σ `→ τ) Γ} {a}
             {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : (Γ -Env) 𝓥^B Δ} →
             𝓡 f ρ^A ρ^B → 𝓡 a ρ^A ρ^B →
             `∀[ 𝓥^R ] ρ^A ρ^B → 𝓡 (f `$ a) ρ^A ρ^B

    R⟦if⟧ :  ∀ {Γ Δ} {σ} {b} {l r : Trm σ Γ}
             {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : _} →
             𝓡 b ρ^A ρ^B → 𝓡 l ρ^A ρ^B → 𝓡 r ρ^A ρ^B →
             `∀[ 𝓥^R ] ρ^A ρ^B → 𝓡 (`if b l r) ρ^A ρ^B

    R⟦let⟧ :  ∀ {Γ Δ} {σ τ} {M : Trm σ Γ} {N : Trm τ (Γ ∙ σ)}
              {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : (Γ -Env) 𝓥^B Δ}
              (rM : 𝓡 M ρ^A ρ^B) →
              (rN : ∀ {Θ} {u^A : 𝓥^A σ Θ} {u^B : 𝓥^B σ Θ} →
                  ∀ inc → rmodel 𝓥^R u^A u^B →
                    let  ρ^A′ = ext^A ρ^A inc u^A
                         ρ^B′ = ext^B ρ^B inc u^B
                    in 𝓡 N ρ^A′ ρ^B′) →
              `∀[ 𝓥^R ] ρ^A ρ^B → 𝓡 (`let M N) ρ^A ρ^B

{-
-- phew!
module Simulate {ℓ^EA ℓ^MA ℓ^EB ℓ^MB ℓ^RE ℓ^RM : Level}
 {𝓥^A : PreModel ℓ^EA} {Θ^A : Model 𝓥^A} {𝓔^A : {cbv : CBV} → PreModel ℓ^MA}
 {𝓥^B : PreModel ℓ^EB} {Θ^B : Model 𝓥^B} {𝓔^B : {cbv : CBV} → PreModel ℓ^MB}
 {𝓡𝓥^A : Morphism Θ^A (𝓔^A {cbv = `val})}
 {𝓡𝓣^A : PreMorphism (𝓔^A {cbv = `val}) (𝓔^A {cbv = `trm})}
 {𝓡𝓥^B : Morphism Θ^B (𝓔^B {cbv = `val})}
 {𝓡𝓣^B : PreMorphism (𝓔^B {cbv = `val}) (𝓔^B {cbv = `trm})}
 {𝓢^A : Semantics {Θ = Θ^A} {𝓔 = λ {f} → 𝓔^A {cbv = f}} 𝓡𝓥^A 𝓡𝓣^A}
 {𝓢^B : Semantics {Θ = Θ^B} {𝓔 = λ {f} → 𝓔^B {cbv = f}} 𝓡𝓥^B 𝓡𝓣^B}
 {𝓥^R : RPreModel 𝓥^A 𝓥^B ℓ^RE} {Θ^R : RModel {Θ^A = Θ^A} {Θ^B = Θ^B} 𝓥^R}
 {𝓔^R : {cbv : CBV} → RPreModel (𝓔^A {cbv = cbv}) (𝓔^B {cbv = cbv}) ℓ^RM}
 {VAR^R : RMorphism {𝓥^R = 𝓥^R} 𝓡𝓥^A 𝓡𝓥^B (𝓔^R {cbv = `val})}
 {VAL^R : RPreMorphism (𝓔^R {cbv = `val}) 𝓡𝓣^A 𝓡𝓣^B (𝓔^R {cbv = `trm})}
 (𝓢 : Simulation 𝓢^A 𝓢^B {Θ^R = Θ^R} {𝓔^R = 𝓔^R} VAR^R VAL^R)

 where

  open RModel Θ^R
  open Simulation 𝓢

  lemma : ∀ {cbv} {Γ Δ} {σ} (E : Exp {cbv} σ Γ) →
   {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : (Γ -Env) 𝓥^B Δ} (ρ^R : `∀[ 𝓥^R ] ρ^A ρ^B) →
   rmodel (𝓔^R {cbv = cbv}) (sem^A ρ^A E) (sem^B ρ^B E)

  lemma   (`var v)  ρ^R = R⟦inj⟧ (var^R ρ^R v) where open RMorphism VAR^R

  lemma    (`b b)   ρ^R = R⟦b⟧ b ρ^R
  lemma    (`λ M)   ρ^R = R⟦λ⟧ {M = M} (λ inc u^R → lemma M (th^R ρ^R inc ∙^R u^R)) ρ^R

  lemma   (`val V)  ρ^R = VAL^R (lemma V ρ^R)

  lemma   (f `$ a)  ρ^R = R⟦$⟧ {f = f} {a = a} F A ρ^R
   where F = lemma f ρ^R ; A = lemma a ρ^R
  lemma (`if b l r) ρ^R = R⟦if⟧ {b = b} {l} {r} B L R ρ^R
   where B = lemma b ρ^R ; L = lemma l ρ^R ; R = lemma r ρ^R
  lemma  (`let M N) ρ^R = R⟦let⟧ {M = M} {N = N} lemmaM (λ inc u^R → lemma N (th^R ρ^R inc ∙^R u^R)) ρ^R
   where lemmaM = lemma M ρ^R


Exp^R : {cbv : CBV} → RPreModel (Exp {cbv}) (Exp {cbv}) _
Exp^R {cbv} = mkRPreModel (λ {σ} {Γ} → _≡_ {A = Exp {cbv} σ Γ})

Val→Val^R : RMorphism Val→Val Val→Val (Exp^R {cbv = `val})
Val→Val^R = mkRInj id -- record { R⟦inj⟧ = id }

Val→Trm^R : RPreMorphism (Exp^R {cbv = `val}) Val→Trm Val→Trm (Exp^R {cbv = `trm})
Val→Trm^R = PEq.cong `val

Subst-ext-sim : Simulation Substitution Substitution
 {Θ^R = mkRModel (λ rel inc → env^R (λ v → PEq.cong (inc *-Var_) (var^R rel v)))}
 {𝓔^R = Exp^R} Val→Val^R Val→Trm^R
Subst-ext-sim = record
 {
 R⟦b⟧ = λ b _ → PEq.refl {x = `b b}
 ;
 R⟦λ⟧ = λ L _ → PEq.cong λλ (L weak (PEq.refl {x = val₀}))
 ;
 R⟦$⟧ = λ F A _ → PEq.cong₂ $$ F A
 ;
 R⟦if⟧ = λ B L R _ → PEq.cong₂ (uncurry IF) (PEq.cong₂ _,_ B L) R
 ;
 R⟦let⟧ = λ M N _ → PEq.cong₂ LET M (N weak (PEq.refl {x = val₀}))
 } where open Model₀ 𝓥al₀

Subst-ext : ∀ {f} {Γ Δ} {σ} → (E : Exp {f} σ Γ) →
 {ρ ρ' : Γ ⊨ Δ} → (∀ {τ} v → var ρ {τ} v ≡ var ρ' v) → subst E ρ ≡ subst E ρ'
Subst-ext E relρ = lemma E (env^R relρ)
 where open Simulate Subst-ext-sim
-}
