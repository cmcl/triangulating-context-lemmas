{-- Using the generic Allais et al. machinery to prove simulation lemmas. -}
module simulation-lemmas where

open import Level as L using (Level ; _⊔_)
open import Data.Product hiding (map)
open import Function as F hiding (_∋_ ; _$_)

open import Relation.Binary.PropositionalEquality as PEq using (_≡_)

open import lambda-fg
open import acmm
open import simulation

-- Extensionality of substitution
Subst-ext-sim : Simulation Substitution Substitution
 {Θ^R = mkRModel (λ rel inc →
                    env^R (λ v → PEq.cong (inc *-Var_) (var^R rel v)))}
 {𝓔^R = Exp^R} Val→Val^R Val→Trm^R
Subst-ext-sim = record
 {
 R⟦b⟧ = λ b _ → PEq.refl {x = `b b}
 ;
 R⟦λ⟧ = λ L _ → PEq.cong λλ (L weak (PEq.refl {x = val₀}))
 ;
 R⟦$⟧ = λ F A _ → PEq.cong₂ _`$_ F A
 ;
 R⟦if⟧ = λ B L R _ → PEq.cong₂ (uncurry `if) (PEq.cong₂ _,_ B L) R
 ;
 R⟦let⟧ = λ M N _ → PEq.cong₂ `let M (N weak (PEq.refl {x = val₀}))
 } where open Model₀ 𝓥al₀

Subst-ext : ∀ {f} {Γ Δ} {σ} → (E : Exp {f} σ Γ) →
 {ρ ρ' : Γ ⊨ Δ} → (∀ {τ} v → var ρ {τ} v ≡ var ρ' v) → subst E ρ ≡ subst E ρ'
Subst-ext E relρ = lemma E (env^R relρ)
 where open Simulate Subst-ext-sim
