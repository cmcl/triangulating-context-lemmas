{-- ACMM simulation and fusion frameworks for proving properties of
 -- semantics. -}
module logical-predicates where

open import Level as L using (Level ; _⊔_)
open import Data.Product hiding (map)
open import Function as F hiding (_∋_ ; _$_)

open import Relation.Binary.PropositionalEquality as PEq using (_≡_)

open import lambda-fg
open import acmm

-- A predicate premodel
record PPreModel {ℓ^A : Level} (𝓔^A : PreModel ℓ^A) 
        (ℓ^P : Level) : Set (ℓ^A ⊔ L.suc ℓ^P) where
  constructor mkPPreModel
  field pmodel : {σ : Ty} → [ 𝓔^A σ ⟶ const (Set ℓ^P) ]
open PPreModel public

-- The pointwise lifting of a predicate premodel to contexts.
record `∀^P[_] {ℓ^A ℓ^P : Level}
      {𝓔^A : PreModel ℓ^A} (𝓔^P : PPreModel 𝓔^A ℓ^P)
      {Γ Δ : Cx} (ρ^A : (Γ -Env) 𝓔^A Δ) : Set ℓ^P where
  constructor env^P
  field var^P : {σ : Ty} (v : Var σ Γ) →
                   pmodel 𝓔^P {σ} {Δ} (var ρ^A v) 
open `∀^P[_] public

-- Predicated enviornments can be extended with predicated elements.
infixl 10 _∙^P_
_∙^P_ :  ∀ {ℓ^A ℓ^P : Level}
    {𝓔^A : PreModel ℓ^A} {𝓔^P : PPreModel 𝓔^A ℓ^P}
    {Δ Γ} {ρ^A : (Γ -Env) 𝓔^A Δ} {σ} {u^A : 𝓔^A σ Δ} →
 `∀^P[ 𝓔^P ] ρ^A → pmodel 𝓔^P u^A → `∀^P[ 𝓔^P ] (ρ^A `∙ u^A)
var^P (ρ^P ∙^P u^P)   ze   = u^P
var^P (ρ^P ∙^P u^P) (su v) = var^P ρ^P v

-- A predicate model is a predicate premodel whose predicated environments can
-- be thinned (and are still predicated).
record PModel {ℓ^A ℓ^P : Level}
              {𝓥^A : PreModel ℓ^A} {Θ^A : Model 𝓥^A}
              (𝓥^P : PPreModel 𝓥^A ℓ^P) : Set (ℓ^A ⊔ L.suc ℓ^P)
 where

  constructor mkPModel

  th^A = Thin.th Θ^A

  field

   th^P : ∀ {Γ Δ} → {ρ^A : (Γ -Env) 𝓥^A Δ} →
             `∀^P[ 𝓥^P ] ρ^A → {Θ : Cx} (inc : Δ ⊆ Θ) →
             `∀^P[ 𝓥^P ] (th^A ρ^A inc) 

-- Predicated values that inject into terms map to predicated terms.
RPreMorphism : {ℓ^A ℓ^M ℓ^PV ℓ^PT : Level}
 {𝓥^A : PreModel ℓ^A} {𝓣^A : PreModel ℓ^M}
 (𝓥^P : PPreModel 𝓥^A ℓ^PV)
 (inj^A : PreMorphism 𝓥^A 𝓣^A) 
 (𝓣^P  : PPreModel 𝓣^A ℓ^PT) → Set (ℓ^PV ⊔ ℓ^PT ⊔ ℓ^A)
RPreMorphism 𝓥^P inj^A 𝓣^P =
 ∀ {Γ} {σ} {a} → pmodel 𝓥^P {σ} {Γ} a → pmodel 𝓣^P (inj^A a) 

-- TODO: Enforce the value predicate premodel to be a model?
record RMorphism {ℓ^A ℓ^M ℓ^PV ℓ^PT : Level}
   {𝓥^A : PreModel ℓ^A} {Θ^A : Model 𝓥^A}
   {𝓣^A : PreModel ℓ^M}
   {𝓥^P  : PPreModel 𝓥^A ℓ^PV}
   -- (Θ^P : PModel {Θ^A = Θ^A} {Θ^B = Θ^B} 𝓥^P)
   (𝓘^A : Morphism Θ^A 𝓣^A) 
   (𝓣^P  : PPreModel 𝓣^A ℓ^PT) : Set (ℓ^PV ⊔ ℓ^PT ⊔ ℓ^A ⊔ ℓ^M)
 where

 constructor mkRInj

 inj^A = Morphism.inj 𝓘^A

 field
   P⟦inj⟧ : RPreMorphism 𝓥^P inj^A 𝓣^P

record LogicalPredicate {ℓ^A ℓ^M ℓ^PV ℓ^PT : Level}
 {𝓥^A : PreModel ℓ^A} {Θ^A : Model 𝓥^A} {𝓔^A : {f : CBV} → PreModel ℓ^M}
 {var^A : Morphism Θ^A (𝓔^A {`val})} -- injection of variables into
                                         -- values.
 {val^A : PreMorphism (𝓔^A {`val}) (𝓔^A {`trm})} -- values to term
                                                         -- injection.
 (𝓢^A : Semantics {Θ = Θ^A} {𝓔 = λ {f} → 𝓔^A {f}} var^A val^A)

 {𝓥^P : PPreModel 𝓥^A ℓ^PV} {Θ^P : PModel {Θ^A = Θ^A} 𝓥^P}

 {𝓔^P : {f : CBV} → PPreModel (𝓔^A {f}) ℓ^PT}

 (var^P : RMorphism {𝓥^P = 𝓥^P} var^A (𝓔^P {`val}))
 (val^P : RPreMorphism (𝓔^P {`val}) val^A (𝓔^P {`trm}))

 : Set (ℓ^PV ⊔ ℓ^A ⊔ ℓ^M ⊔ ℓ^PT)

 where

  th^A  = Thin.th Θ^A
  ext^A  = Thin.ext Θ^A
  sem^A  = Eval.sem 𝓢^A

  𝓟 : ∀ {f} {Γ Δ} {σ} →
      Exp {f} σ Γ → (Γ -Env) 𝓥^A Δ → Set (ℓ^PT)
  𝓟 {f} E ρ^A = pmodel (𝓔^P {f}) (sem^A {f} ρ^A E) 

  infix 4 𝓟[_]_
  𝓟[_]_ : ∀ {f} {Γ Δ} {σ} → Exp {f} σ Γ → (Γ -Env) 𝓥^A Δ → Set (ℓ^PT ⊔ ℓ^PV)
  𝓟[_]_ E ρ^A = `∀^P[ 𝓥^P ] ρ^A → 𝓟 E ρ^A 

  field
    P⟦b⟧  :  ∀ {Γ Δ} {β} → (b : ⟦ β ⟧B) →
             {ρ^A : (Γ -Env) 𝓥^A Δ} →
             𝓟[ `b b ] ρ^A --`∀^P[ 𝓥^P ] ρ^A → 𝓟 (`b b) ρ^A 

    P⟦λ⟧ :  ∀ {Γ Δ} {σ τ} {M : Trm τ (Γ ∙ σ)}
            {ρ^A : (Γ -Env) 𝓥^A Δ} 
            (r : ∀ {Θ} {u^A : 𝓥^A σ Θ} →
               ∀ inc → pmodel 𝓥^P u^A →
                 let  ρ^A′ = ext^A ρ^A inc u^A
                 in 𝓟 M ρ^A′) →
            𝓟[ `λ M ] ρ^A

    P⟦$⟧  :  ∀ {Γ Δ} {σ τ} {f : Val (σ `→ τ) Γ} {a}
             {ρ^A : (Γ -Env) 𝓥^A Δ} →
             𝓟 f ρ^A → 𝓟 a ρ^A → 𝓟[ f `$ a ] ρ^A

    P⟦if⟧ :  ∀ {Γ Δ} {σ} {b} {l r : Trm σ Γ}
             {ρ^A : (Γ -Env) 𝓥^A Δ} →
             𝓟 b ρ^A → 𝓟 l ρ^A → 𝓟 r ρ^A →
             𝓟[ `if b l r ] ρ^A

    P⟦let⟧ :  ∀ {Γ Δ} {σ τ} {M : Trm σ Γ} {N : Trm τ (Γ ∙ σ)}
              {ρ^A : (Γ -Env) 𝓥^A Δ} 
              (rM : 𝓟 M ρ^A) →
              (rN : ∀ {Θ} {u^A : 𝓥^A σ Θ} →
                  ∀ inc → pmodel 𝓥^P u^A →
                    let  ρ^A′ = ext^A ρ^A inc u^A
                    in 𝓟 N ρ^A′) →
              𝓟[ `let M N ] ρ^A

-- phew!
module LogicalPredicateLemma {ℓ^A ℓ^M ℓ^PV ℓ^PT : Level}
 {𝓥^A : PreModel ℓ^A} {Θ^A : Model 𝓥^A} {𝓔^A : {f : CBV} → PreModel ℓ^M}

 {var^A : Morphism Θ^A (𝓔^A {`val})}
 {val^A : PreMorphism (𝓔^A {`val}) (𝓔^A {`trm})}

 {𝓢^A : Semantics {Θ = Θ^A} {𝓔 = λ {f} → 𝓔^A {f}} var^A val^A}

 {𝓥^P : PPreModel 𝓥^A ℓ^PV} {Θ^P : PModel {Θ^A = Θ^A} 𝓥^P}

 {𝓔^P : {f : CBV} → PPreModel (𝓔^A {f}) ℓ^PT}

 {VAR^P : RMorphism {𝓥^P = 𝓥^P} var^A (𝓔^P {`val})}
 {VAL^P : RPreMorphism (𝓔^P {`val}) val^A (𝓔^P {`trm})}
 (𝓛𝓟 : LogicalPredicate 𝓢^A {Θ^P = Θ^P} {𝓔^P = 𝓔^P} VAR^P VAL^P)

 where

  open PModel Θ^P
  open LogicalPredicate 𝓛𝓟

  lemma : ∀ {f} {Γ Δ} {σ} (E : Exp {f} σ Γ) →
          {ρ^A : (Γ -Env) 𝓥^A Δ} → 𝓟[ E ] ρ^A
-- `∀^P[ 𝓥^P ] ρ^A → pmodel (𝓔^P {f}) (sem^A ρ^A E) 

  lemma (`var v) ρ^P = P⟦inj⟧ (var^P ρ^P v) where open RMorphism VAR^P

  lemma (`b b) ρ^P = P⟦b⟧ b ρ^P
  lemma (`λ M) ρ^P =
    P⟦λ⟧ {M = M} (λ inc u^P → lemma M (th^P ρ^P inc ∙^P u^P)) ρ^P

  lemma (`val V) ρ^P = VAL^P (lemma V ρ^P)

  lemma (f `$ a)  ρ^P = P⟦$⟧ {f = f} {a = a} F A ρ^P
   where F = lemma f ρ^P ; A = lemma a ρ^P
  lemma (`if b l r) ρ^P = P⟦if⟧ {b = b} {l} {r} B L R ρ^P
   where B = lemma b ρ^P ; L = lemma l ρ^P ; R = lemma r ρ^P
  lemma (`let M N) ρ^P =
    P⟦let⟧ {M = M} {N = N} lemmaM
                           (λ inc u^P → lemma N (th^P ρ^P inc ∙^P u^P)) ρ^P
   where lemmaM = lemma M ρ^P

{-
Exp^P : {f : CBV} → PPreModel (Exp {f}) (Exp {f}) _
Exp^P {f} = mkPPreModel (λ {σ} {Γ} → _≡_ {A = Exp {f} σ Γ})

VarVal^P : PPreModel Var Val _
VarVal^P = mkPPreModel (λ v V → `var v ≡ V)

Var→Val^P : RMorphism Var→Val Var→Val (Exp^P {`val})
Var→Val^P = mkRInj (PEq.cong `var)

Val→Val^P : RMorphism Val→Val Val→Val (Exp^P {`val})
Val→Val^P = mkRInj id -- record { P⟦inj⟧ = id }

Val→Trm^P : RPreMorphism (Exp^P {`val}) Val→Trm Val→Trm (Exp^P {`trm})
Val→Trm^P = PEq.cong `val

record Fusion {ℓ^A ℓ^L ℓ^B ℓ^M ℓ^C ℓ^N ℓ^PVBC ℓ^PV ℓ^PT : Level}
 {𝓥^A : PreModel ℓ^A} {Θ^A : Model 𝓥^A} {𝓔^A : {f : CBV} → PreModel ℓ^L}
 {𝓥^B : PreModel ℓ^B} {Θ^B : Model 𝓥^B} {𝓔^B : {f : CBV} → PreModel ℓ^M}
 {𝓥^C : PreModel ℓ^C} {Θ^C : Model 𝓥^C} {𝓔^C : {f : CBV} → PreModel ℓ^N}

 {var^A : Morphism Θ^A (𝓔^A {`val})} -- injection of variables into
                                         -- values.
 {val^A : PreMorphism (𝓔^A {`val}) (𝓔^A {`trm})} -- values to term
                                                         -- injection.
 -- Analogous maps for 𝓔^B and 𝓔^C.
 {var^B : Morphism Θ^B (𝓔^B {`val})}
 {val^B : PreMorphism (𝓔^B {`val}) (𝓔^B {`trm})}

 {var^C : Morphism Θ^C (𝓔^C {`val})}
 {val^C : PreMorphism (𝓔^C {`val}) (𝓔^C {`trm})}

 (𝓢^A : Semantics {Θ = Θ^A} {𝓔 = λ {f} → 𝓔^A {f}} var^A val^A)
 (𝓢^B : Semantics {Θ = Θ^B} {𝓔 = λ {f} → 𝓔^B {f}} var^B val^B)
 (𝓢^C : Semantics {Θ = Θ^C} {𝓔 = λ {f} → 𝓔^C {f}} var^C val^C)

 (𝓥^P-BC : PPreModel 𝓥^B 𝓥^C ℓ^PVBC)

 (𝓥^P : {Γ Δ Θ : Cx} →
         (Γ -Env) 𝓥^A Δ → (Δ -Env) 𝓥^B Θ → (Γ -Env) 𝓥^C Θ → Set (ℓ^PV))

 (𝓔^P : {f : CBV} → PPreModel (𝓔^B {f}) (𝓔^C {f}) ℓ^PT)

 : Set (ℓ^PV ⊔ ℓ^PVBC ⊔ ℓ^A ⊔ ℓ^B ⊔ ℓ^C ⊔ ℓ^L ⊔ ℓ^M ⊔ ℓ^N ⊔ ℓ^PT)
 where
  th^A  = Thin.th Θ^A
  th^B  = Thin.th Θ^B
  th^C  = Thin.th Θ^C
  ext^A  = Thin.ext Θ^A
  ext^B  = Thin.ext Θ^B
  ext^C  = Thin.ext Θ^C
  sem^A  = Eval.sem 𝓢^A
  sem^B  = Eval.sem 𝓢^B
  sem^C  = Eval.sem 𝓢^C

  field
    reifyₐ : {f : CBV} {σ : Ty} → [ (𝓔^A {f}) σ  ⟶ Exp {f} σ ]

    varₐ₀  : {σ : Ty} → [ σ ⊢ 𝓥^A σ ]

  𝓟 : ∀ {f} {Γ Δ Θ} {σ} → Exp {f} σ Γ →
      (Γ -Env) 𝓥^A Δ → (Δ -Env) 𝓥^B Θ → (Γ -Env) 𝓥^C Θ → Set (ℓ^PT)
  𝓟 {f} E ρ^A ρ^B ρ^C =
    pmodel (𝓔^P {f}) (sem^B ρ^B (reifyₐ (sem^A {f} ρ^A E))) (sem^C {f} ρ^C E)

  𝓟[_] : ∀ {f} {Γ Δ Θ} {σ} → Exp {f} σ Γ →
         (Γ -Env) 𝓥^A Δ → (Δ -Env) 𝓥^B Θ → (Γ -Env) 𝓥^C Θ → Set (ℓ^PT ⊔ ℓ^PV)
  𝓟[_] E ρ^A ρ^B ρ^C = 𝓥^P ρ^A ρ^B ρ^C → 𝓟 E ρ^A ρ^B ρ^C

  field
    𝓥^P∙ : ∀ {Γ Δ Θ} {σ} {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : (Δ -Env) 𝓥^B Θ}
           {ρ^C : (Γ -Env) 𝓥^C Θ} {u^B : 𝓥^B σ Θ} {u^C} →
           𝓥^P ρ^A ρ^B ρ^C → pmodel 𝓥^P-BC u^B u^C →
           𝓥^P (th^A ρ^A weak `∙ varₐ₀) (ρ^B `∙ u^B) (ρ^C `∙ u^C)

    𝓥^Pth : ∀ {Γ Δ Θ} {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : (Δ -Env) 𝓥^B Θ}
            {ρ^C : (Γ -Env) 𝓥^C Θ} {Ξ : Cx} (inc : Θ ⊆ Ξ) →
            𝓥^P ρ^A ρ^B ρ^C →
            𝓥^P ρ^A (th^B ρ^B inc) (th^C ρ^C inc)

    P⟦b⟧  :  ∀ {Γ Δ Θ} {β} → (b : ⟦ β ⟧B) →
             {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : (Δ -Env) 𝓥^B Θ}
             {ρ^C : (Γ -Env) 𝓥^C Θ} →
             𝓟[ `b b ] ρ^A ρ^B ρ^C

    P⟦var⟧ : ∀ {Γ Δ Θ} {σ} → (v : Var σ Γ) →
             {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : (Δ -Env) 𝓥^B Θ}
             {ρ^C : (Γ -Env) 𝓥^C Θ} →
             𝓟[ `var v ] ρ^A ρ^B ρ^C

    P⟦λ⟧ :  ∀ {Γ Δ Θ} {σ τ} {M : Trm τ (Γ ∙ σ)}
            {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : (Δ -Env) 𝓥^B Θ}
            {ρ^C : (Γ -Env) 𝓥^C Θ}
            (r : ∀ {Θ} {u^B : 𝓥^B σ Θ} {u^C : 𝓥^C σ Θ} →
               ∀ inc → pmodel 𝓥^P-BC u^B u^C →
                 let ρ^A′ = th^A ρ^A weak `∙ varₐ₀
                     ρ^B′ = ext^B ρ^B inc u^B
                     ρ^C′ = ext^C ρ^C inc u^C
                 in 𝓟 M ρ^A′ ρ^B′ ρ^C′) →
            𝓟[ `λ M ] ρ^A ρ^B ρ^C

    P⟦val⟧  :  ∀ {Γ Δ Θ} {σ} {V : Val σ Γ}
               {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : (Δ -Env) 𝓥^B Θ}
               {ρ^C : (Γ -Env) 𝓥^C Θ} →
               𝓟 V ρ^A ρ^B ρ^C → 𝓟[ `val V ] ρ^A ρ^B ρ^C

    P⟦$⟧  :  ∀ {Γ Δ Θ} {σ τ} {f : Val (σ `→ τ) Γ} {a}
             {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : (Δ -Env) 𝓥^B Θ}
             {ρ^C : (Γ -Env) 𝓥^C Θ} →
             𝓟 f ρ^A ρ^B ρ^C → 𝓟 a ρ^A ρ^B ρ^C → 𝓟[ f `$ a ] ρ^A ρ^B ρ^C


    P⟦if⟧ :  ∀ {Γ Δ Θ} {σ} {b} {l r : Trm σ Γ}
             {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : (Δ -Env) 𝓥^B Θ}
             {ρ^C : (Γ -Env) 𝓥^C Θ} →
             𝓟 b ρ^A ρ^B ρ^C → 𝓟 l ρ^A ρ^B ρ^C → 𝓟 r ρ^A ρ^B ρ^C →
             𝓟[ `if b l r ] ρ^A ρ^B ρ^C

    P⟦let⟧ :  ∀ {Γ Δ Θ} {σ τ} {M : Trm σ Γ} {N : Trm τ (Γ ∙ σ)}
              {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : (Δ -Env) 𝓥^B Θ}
              {ρ^C : (Γ -Env) 𝓥^C Θ}
              (rM : 𝓟 M ρ^A ρ^B ρ^C) →
              (rN : ∀ {Θ} {u^B : 𝓥^B σ Θ} {u^C : 𝓥^C σ Θ} →
                  ∀ inc → pmodel 𝓥^P-BC u^B u^C →
                    let ρ^A′ = th^A ρ^A weak `∙ varₐ₀
                        ρ^B′ = ext^B ρ^B inc u^B
                        ρ^C′ = ext^C ρ^C inc u^C
                    in 𝓟 N ρ^A′ ρ^B′ ρ^C′) →
              𝓟[ `let M N ] ρ^A ρ^B ρ^C

module Fuse {ℓ^A ℓ^L ℓ^B ℓ^M ℓ^C ℓ^N ℓ^PVBC ℓ^PV ℓ^PT : Level}
 {𝓥^A : PreModel ℓ^A} {Θ^A : Model 𝓥^A} {𝓔^A : {f : CBV} → PreModel ℓ^L}
 {𝓥^B : PreModel ℓ^B} {Θ^B : Model 𝓥^B} {𝓔^B : {f : CBV} → PreModel ℓ^M}
 {𝓥^C : PreModel ℓ^C} {Θ^C : Model 𝓥^C} {𝓔^C : {f : CBV} → PreModel ℓ^N}

 {var^A : Morphism Θ^A (𝓔^A {`val})} -- injection of variables into
                                         -- values.
 {val^A : PreMorphism (𝓔^A {`val}) (𝓔^A {`trm})} -- values to term
                                                         -- injection.
 -- Analogous maps for 𝓔^B and 𝓔^C.
 {var^B : Morphism Θ^B (𝓔^B {`val})}
 {val^B : PreMorphism (𝓔^B {`val}) (𝓔^B {`trm})}

 {var^C : Morphism Θ^C (𝓔^C {`val})}
 {val^C : PreMorphism (𝓔^C {`val}) (𝓔^C {`trm})}

 {𝓢^A : Semantics {Θ = Θ^A} {𝓔 = λ {f} → 𝓔^A {f}} var^A val^A}
 {𝓢^B : Semantics {Θ = Θ^B} {𝓔 = λ {f} → 𝓔^B {f}} var^B val^B}
 {𝓢^C : Semantics {Θ = Θ^C} {𝓔 = λ {f} → 𝓔^C {f}} var^C val^C}

 {𝓥^P-BC : PPreModel 𝓥^B 𝓥^C ℓ^PVBC}

 {𝓥^P : {Γ Δ Θ : Cx} →
         (Γ -Env) 𝓥^A Δ → (Δ -Env) 𝓥^B Θ → (Γ -Env) 𝓥^C Θ → Set (ℓ^PV)}

 {𝓔^P : {f : CBV} → PPreModel (𝓔^B {f}) (𝓔^C {f}) ℓ^PT}

 (𝓕 : Fusion 𝓢^A 𝓢^B 𝓢^C 𝓥^P-BC 𝓥^P 𝓔^P)
 where

   open Fusion 𝓕

   lemma : ∀ {f} {Γ Δ Θ} {σ} (E : Exp {f} σ Γ) →
          {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : (Δ -Env) 𝓥^B Θ}
          {ρ^C : (Γ -Env) 𝓥^C Θ} → 𝓟[ E ] ρ^A ρ^B ρ^C

   lemma (`var v) ρ^P = P⟦var⟧ v ρ^P
   lemma (`b b) ρ^P = P⟦b⟧ b ρ^P
   lemma {`val} (`λ M) ρ^P =
     P⟦λ⟧ {M = M} (λ inc u^P → lemma M (𝓥^P∙ (𝓥^Pth inc ρ^P) u^P)) ρ^P
   lemma (`val V) ρ^P = P⟦val⟧ {V = V} (lemma V ρ^P) ρ^P
   lemma (f `$ a) ρ^P = P⟦$⟧ {f = f} {a = a} F A ρ^P
     where F = lemma f ρ^P ; A = lemma a ρ^P
   lemma (`if b l r) ρ^P = P⟦if⟧ {b = b} {l} {r} B L R ρ^P
     where B = lemma b ρ^P ; L = lemma l ρ^P ; R = lemma r ρ^P
   lemma (`let M N) ρ^P =
     P⟦let⟧ {M = M} {N = N} (lemma M ρ^P)
            (λ inc u^P → lemma N (𝓥^P∙ (𝓥^Pth inc ρ^P) u^P)) ρ^P

-- Syntactic fusion results require much fewer assumptions.
record SyntacticFusion {ℓ^A ℓ^B ℓ^C ℓ^PVBC ℓ^PV : Level}
 {𝓥^A : PreModel ℓ^A} {Θ^A : Model 𝓥^A} (mod^A : Model₀ Θ^A)
 {𝓥^B : PreModel ℓ^B} {Θ^B : Model 𝓥^B} (mod^B : Model₀ Θ^B)
 {𝓥^C : PreModel ℓ^C} {Θ^C : Model 𝓥^C} (mod^C : Model₀ Θ^C)

 (var^A : Morphism Θ^A Val) -- injection of variables into
                            -- values.
 -- Analogous maps for 𝓔^B and 𝓔^C.
 (var^B : Morphism Θ^B Val)
 (var^C : Morphism Θ^C Val)

 (𝓥^P-BC : PPreModel 𝓥^B 𝓥^C ℓ^PVBC)
 (𝓥^P : {Γ Δ Θ : Cx} →
         (Γ -Env) 𝓥^A Δ → (Δ -Env) 𝓥^B Θ → (Γ -Env) 𝓥^C Θ → Set (ℓ^PV))

 : Set (ℓ^PV ⊔ ℓ^PVBC ⊔ ℓ^A ⊔ ℓ^B ⊔ ℓ^C)
 where
  th^A  = Thin.th Θ^A
  th^B  = Thin.th Θ^B
  th^C  = Thin.th Θ^C
  ext^A  = Thin.ext Θ^A
  ext^B  = Thin.ext Θ^B
  ext^C  = Thin.ext Θ^C
  sem^A = Eval.sem (syntactic mod^A {var^A})
  sem^B = Eval.sem (syntactic mod^B {var^B})
  sem^C = Eval.sem (syntactic mod^C {var^C})

  𝓟 : ∀ {f} {Γ Δ Θ} {σ} → Exp {f} σ Γ →
      (Γ -Env) 𝓥^A Δ → (Δ -Env) 𝓥^B Θ → (Γ -Env) 𝓥^C Θ → Set
  𝓟 {f} E ρ^A ρ^B ρ^C = sem^B ρ^B (sem^A ρ^A E) ≡ sem^C ρ^C E

  𝓟[_] : ∀ {f} {Γ Δ Θ} {σ} → Exp {f} σ Γ →
         (Γ -Env) 𝓥^A Δ → (Δ -Env) 𝓥^B Θ → (Γ -Env) 𝓥^C Θ → Set (ℓ^PV)
  𝓟[_] E ρ^A ρ^B ρ^C = 𝓥^P ρ^A ρ^B ρ^C → 𝓟 E ρ^A ρ^B ρ^C

  field
    𝓥^P∙ : ∀ {Γ Δ Θ : Cx} {σ : Ty}
           {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : (Δ -Env) 𝓥^B Θ}
           {ρ^C : (Γ -Env) 𝓥^C Θ} {u^B : 𝓥^B σ Θ} {u^C : 𝓥^C σ Θ} →
           (ρ^P : 𝓥^P ρ^A ρ^B ρ^C) → (u^P : pmodel 𝓥^P-BC u^B u^C) →
           𝓥^P (th^A ρ^A weak `∙ Model₀.var₀ mod^A) (ρ^B `∙ u^B) (ρ^C `∙ u^C)

    𝓥^Pth : ∀ {Γ Δ Θ} {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : (Δ -Env) 𝓥^B Θ}
            {ρ^C : (Γ -Env) 𝓥^C Θ} {Ξ : Cx} (inc : Θ ⊆ Ξ) →
            𝓥^P ρ^A ρ^B ρ^C →
            𝓥^P ρ^A (th^B ρ^B inc) (th^C ρ^C inc)

    P⟦var⟧ : ∀ {Γ Δ Θ} {σ} → (v : Var σ Γ) →
             {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : (Δ -Env) 𝓥^B Θ}
             {ρ^C : (Γ -Env) 𝓥^C Θ} →
             𝓟[ `var v ] ρ^A ρ^B ρ^C

    var₀-BC : {Γ : Cx} {σ : Ty} →
              pmodel 𝓥^P-BC {σ} {Γ ∙ σ}
                     (Model₀.var₀ mod^B) (Model₀.var₀ mod^C)
-}
