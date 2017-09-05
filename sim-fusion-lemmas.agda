{-- Using the generic Allais et al. machinery to prove simulation and fusion
 -- results. -}
module sim-fusion-lemmas where

open import Level as L using (Level ; _⊔_)
open import Data.Product hiding (map)
open import Function as F hiding (_∋_ ; _$_)

open import Relation.Binary.PropositionalEquality as PEq using (_≡_)

open import lambda-fg
open import acmm
open import sim-fusion

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

-- simple instance of the fundamental Simulation lemma
subst-ext : ∀ {f} {Γ Δ} {σ} → (E : Exp {f} σ Γ) →
 {ρ ρ' : Γ ⊨ Δ} → (∀ {τ} v → var ρ {τ} v ≡ var ρ' v) → subst E ρ ≡ subst E ρ'
subst-ext E relρ = lemma E (env^R relρ)
 where open Simulate Subst-ext-sim

subst-ext₀ : ∀ {σ} → (M : Trm₀ σ) (ρ : Env₀ ε) → subst M ρ ≡ subst M ι^Env
subst-ext₀ M ρ = subst-ext M {ρ = ρ} {ρ' = ι^Env {ε}} (λ ())

-- Extensionality of renaming
Ren-ext-sim : Simulation Renaming Renaming
 {Θ^R = mkRModel (λ rel inc →
                    env^R (λ v → PEq.cong (var inc) (var^R rel v)))}
 {𝓔^R = Exp^R} Var→Val^R Val→Trm^R
Ren-ext-sim = record
 {
 R⟦b⟧ = λ b _ → PEq.refl {x = `b b}
 ;
 R⟦λ⟧ = λ L _ → PEq.cong λλ (L weak (PEq.refl {x = var₀}))
 ;
 R⟦$⟧ = λ F A _ → PEq.cong₂ _`$_ F A
 ;
 R⟦if⟧ = λ B L R _ → PEq.cong₂ (uncurry `if) (PEq.cong₂ _,_ B L) R
 ;
 R⟦let⟧ = λ M N _ → PEq.cong₂ `let M (N weak (PEq.refl {x = var₀}))
 } where open Model₀ 𝓥ar₀

ren-ext : ∀ {f} {Γ Δ} {σ} → (E : Exp {f} σ Γ) →
 {r r' : Γ ⊆ Δ} → (∀ {τ} v → var r {τ} v ≡ var r' v) → ren E r ≡ ren E r'
ren-ext E relr = lemma E (env^R relr)
 where open Simulate Ren-ext-sim

-- composition of valuations: sub-sub fusion
_*-Sub_ : ∀ {Γ Δ Ξ} → (ρ : Δ ⊨ Ξ) → (ρ' : Γ ⊨ Δ) → Γ ⊨ Ξ
ρ *-Sub ρ' = map-Env (ρ *-Val_) ρ'

lemma33 : ∀ {f} {Γ Δ Ξ} {σ} → (ρ : Δ ⊨ Ξ) → (ρ' : Γ ⊨ Δ) → (E : Exp {f} σ Γ) →
 ((ρ *-Sub ρ') *-Val E) ≡ (ρ *-Val (ρ' *-Val E))
lemma33 ρ ρ' (`var v) = PEq.refl
lemma33 ρ ρ' (`b b)  = PEq.refl
lemma33 ρ ρ' (`λ M)  = PEq.cong λλ (lemma33 (ext₀^Env ρ) (ext₀^Env ρ') M)
lemma33 ρ ρ' (`val V) rewrite lemma33 ρ ρ' V = PEq.refl
lemma33 ρ ρ' (f `$ a) rewrite lemma33 ρ ρ' f | lemma33 ρ ρ' a = PEq.refl
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

lemma33-ren : ∀ {f} {Γ Δ Ξ} {σ} → (r : Δ ⊆ Ξ) → (r' : Γ ⊆ Δ) →
  (E : Exp {f} σ Γ) → (trans^Var r' r *-Var E) ≡ (r *-Var (r' *-Var E))
lemma33-ren r r' (`var v) = PEq.refl
lemma33-ren r r' (`b b)  = PEq.refl
lemma33-ren r r' (`λ M)  =
  PEq.cong λλ (lemma33-ren (ext₀^Var r) (ext₀^Var r') M)
lemma33-ren r r' (`val V) rewrite lemma33-ren r r' V = PEq.refl
lemma33-ren r r' (f `$ a) rewrite lemma33-ren r r' f | lemma33-ren r r' a =
  PEq.refl
lemma33-ren r r' (`if B L R) rewrite lemma33-ren r r' B | lemma33-ren r r' L |
                                 lemma33-ren r r' R = PEq.refl
lemma33-ren r r'  (`let M N) rewrite lemma33-ren r r' M =
  PEq.cong (`let _) (lemma33-ren (ext₀^Var r) (ext₀^Var r') N)

ext₀^Var-ext : ∀ {Γ Δ} {σ} → {r r' : Γ ⊆ Δ} →
                 (∀ {τ} v → var r {τ} v ≡ var r' v) →
 ∀ {τ} v → var (ext₀^Var {σ} {Γ} r) {τ} v ≡ var (ext₀^Var r') v
ext₀^Var-ext {Γ} {Δ} {σ} {r} {r'} eq =
  [ P ][ PEq.refl ,,,  PEq.cong su ∘ eq ]
 where P = λ {τ} v → var (ext₀^Var {σ} {Γ} r) {τ} v ≡ var (ext₀^Var r') v

-- The same proof as for ext₀^Env-ext₀ but I cannot think how to generalise
-- the statement to encompass both.
ext₀^Env^Var-ext₀ : ∀ {Γ Δ} {σ} → {r : Γ ⊆ Δ} → {ρ : Δ ⊨ Γ} →
  (∀ {τ} v → var ρ {τ} (var r v) ≡ `var v) →
 ∀ {τ} v → var (ext₀^Env {σ} {Δ} ρ) {τ} (var (ext₀^Var r) v) ≡ `var v
ext₀^Env^Var-ext₀ {Γ} {Δ} {σ} {r} {ρ} eq =
  [ P ][ PEq.refl ,,, (PEq.cong (weak *-Var_)) ∘ eq ]
  where
    P = λ {τ} v → var (ext₀^Env {σ} {Δ} ρ) {τ} (var (ext₀^Var r) v) ≡ `var v

-- TODO: Come up with a more informative name for this lemma.
ren-sub : ∀ {f} {Γ Δ} {σ} → (E : Exp {f} σ Γ) → (r : Γ ⊆ Δ) → (ρ : Δ ⊨ Γ) →
  (∀ {τ} v → var ρ {τ} (var r v) ≡ `var v) →
  subst (r *-Var E) ρ ≡ E
ren-sub (`var v) r ρ prf = prf v
ren-sub (`b b) r ρ prf = PEq.refl
ren-sub (`λ M) r ρ prf
  with ren-sub M (ext₀^Var r) (ext₀^Env ρ) (ext₀^Env^Var-ext₀ {ρ = ρ} prf)
... | ih rewrite ih = PEq.refl
ren-sub (`val M) r ρ prf rewrite ren-sub M r ρ prf = PEq.refl
ren-sub (F `$ A) r ρ prf
  rewrite ren-sub F r ρ prf | ren-sub A r ρ prf = PEq.refl
ren-sub (`if B L R) r ρ prf
  rewrite ren-sub B r ρ prf | ren-sub L r ρ prf | ren-sub R r ρ prf = PEq.refl
ren-sub (`let M N) r ρ prf rewrite ren-sub M r ρ prf
  with ren-sub N (ext₀^Var r) (ext₀^Env ρ) (ext₀^Env^Var-ext₀ {ρ = ρ} prf)
... | ih rewrite ih = PEq.refl

-- weakening commutes with renaming by extension.
weak-ext₀^Var-comm : ∀ {Γ Δ} {σ} {r : Γ ⊆ Δ} →
 ∀ {τ} v → var weak {τ} (var r v) ≡ var (ext₀^Var {σ} r) (var weak v)
weak-ext₀^Var-comm v = PEq.refl

-- Weakeing commutes with substitution by extension.
ext₀^Env-weak-comm : ∀ {Γ Δ} {σ} (ρ : Γ ⊨ Δ) →
  ∀ {τ} v → var (ext₀^Env {σ} ρ) {τ} (var weak v) ≡ (weak *-Var (var ρ v))
ext₀^Env-weak-comm ρ v = PEq.refl

-- If combinations of renamings and substitutions are extensionally equal so
-- are there extensions.
ext₀^Env-ext^Var : ∀ {Γ Δ Ξ Ω} {σ}
  {r : Γ ⊆ Δ} {r' : Ω ⊆ Ξ} {ρ : Δ ⊨ Ξ} {ρ' : Γ ⊨ Ω} →
  (∀ {τ} v → var ρ {τ} (var r v) ≡ (r' *-Var (var ρ' v))) →
 ∀ {τ} v → var (ext₀^Env {σ} ρ) {τ}
              (var (ext₀^Var r) v) ≡ (ext₀^Var r' *-Var (var (ext₀^Env ρ') v))
ext₀^Env-ext^Var eq ze = PEq.refl
ext₀^Env-ext^Var {σ = σ} {r' = r'} {ρ' = ρ'} eq (su v)
  with (PEq.cong (weak {σ = σ} *-Var_) ∘ eq) v
... | H rewrite PEq.sym (lemma33-ren (ext₀^Var {σ} r') weak (var ρ' v)) =
  PEq.trans H (PEq.trans (PEq.sym (lemma33-ren weak r' (var ρ' v)))
                         (ren-ext (var ρ' v) (weak-ext₀^Var-comm {r = r'})))

ren-sub-prop : ∀ {f} {Γ Δ Ξ Ω} {σ} →
  (E : Exp {f} σ Γ) → (r : Γ ⊆ Δ) → (r' : Ω ⊆ Ξ)
  (ρ : Δ ⊨ Ξ) → (ρ' : Γ ⊨ Ω) →
  (∀ {τ} v → var ρ {τ} (var r v) ≡ (r' *-Var (var ρ' v))) →
  subst (r *-Var E) ρ ≡ (r' *-Var (subst E ρ'))
ren-sub-prop (`var x) r r' ρ ρ' prf = prf x
ren-sub-prop (`b b) r r' ρ ρ' prf = PEq.refl
ren-sub-prop (`λ M) r r' ρ ρ' prf
  rewrite ren-sub-prop M (ext₀^Var r) (ext₀^Var r') (ext₀^Env ρ) (ext₀^Env ρ')
                      (ext₀^Env-ext^Var {r = r} {r'} {ρ} {ρ'} prf) = PEq.refl
ren-sub-prop (`val M) r r' ρ ρ' prf
  rewrite ren-sub-prop M r r' ρ ρ' prf = PEq.refl
ren-sub-prop (F `$ A) r r' ρ ρ' prf
  rewrite ren-sub-prop F r r' ρ ρ' prf |
          ren-sub-prop A r r' ρ ρ' prf = PEq.refl
ren-sub-prop (`if B L R) r r' ρ ρ' prf
  rewrite ren-sub-prop B r r' ρ ρ' prf |
          ren-sub-prop L r r' ρ ρ' prf |
          ren-sub-prop R r r' ρ ρ' prf = PEq.refl
ren-sub-prop (`let M N) r r' ρ ρ' prf
  rewrite ren-sub-prop M r r' ρ ρ' prf |
          ren-sub-prop N (ext₀^Var r) (ext₀^Var r') (ext₀^Env ρ) (ext₀^Env ρ')
                      (ext₀^Env-ext^Var {r = r} {r'} {ρ} {ρ'} prf)= PEq.refl

-- Special case of ren-sub: weakening and a single substition.
weak-sub : ∀ {f} {Γ} {σ τ} → (V : Val τ Γ) → (E : Exp {f} σ Γ) →
  (weak *-Var E) ⟨ V /var₀⟩ ≡ E
weak-sub V E = ren-sub E weak (ι^Env `∙ V) (λ v → PEq.refl)
