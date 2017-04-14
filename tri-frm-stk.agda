{-# OPTIONS --copatterns #-}
module tri-frm-stk where

open import Data.Bool renaming (true to tt ; false to ff)
open import Data.Product hiding (map)
open import Function as F hiding (_∋_ ; _$_)
open import Level as L using (Level ; _⊔_)

open import Relation.Binary.PropositionalEquality as PEq using (_≡_)

open import lambda-fg
open import acmm
open import relations
open import big-step-prop
open import obs-apx
open import frm-stk-prop

-- Lemma regarding Val to <Frm,Trm> configuration relation transformer
lemma-[_]^F-refl : {ℓ^V : Level} {σ τ : Ty} {R : GRel^V {ℓ^V} {σ}}
  (r : (V : Val₀ σ) → R V V) → (S : Frm σ τ) → (M : Trm₀ τ) →
  S , M [ R ]^F S , M
lemma-[ r ]^F-refl S M {U = U} der = U , der , r U

-- Now prove directly that contextual approximation/simulation implies
-- ``applicative frame stack'' approximation (ciu-sim)

mutual

  ciu-sim₀ : GRel₀^E
  ciu-sim₀ = λ { {`val} → ciu-sim₀^V ; {`trm} → ciu-sim₀^T }

  data ciu-sim₀^B : GRel₀^B where
    ciu-sim₀^B-b : ∀ {β} {b b'} → sim₀^B {β} b b' → ciu-sim₀^B {β} b b'

  data ciu-sim₀^V : GRel₀^V where
    ciu-sim₀^V-b : ∀ {β} {b b'} → ciu-sim₀^B {β} b b' →
      ciu-sim₀^V {`b β} (`b b) (`b b)

    ciu-sim₀^V-λ : ∀ {σ τ} {M N} →
      (∀ U → ciu-sim₀^T {τ} (M ⟨ U /var₀⟩) (N ⟨ U /var₀⟩)) →
      ciu-sim₀^V {σ `→ τ} (`λ M) (`λ N)

  ciu-sim₀^T : GRel₀^T
  ciu-sim₀^T {τ} M N = ∀ {σ} {S} → S , M [ sim₀^V {σ} ]^F S , N

Ciu-sim : ∀ (f : CBV) → Set₁
Ciu-sim f = ∀ {Γ} {τ} → Rel^E {f} {L.zero} {Γ} {τ}
ciu-sim : ∀ {f} → Ciu-sim f
ciu-sim {f} = case f return Ciu-sim of λ { `val →  simV ; `trm → simT  }
 where
  simV : Ciu-sim `val
  simT : Ciu-sim `trm
  simV {Γ} {τ} = _[ simT {Γ} {τ} ]^V_
  simT {Γ} {τ} = _[ ciu-sim₀ {`trm} {τ} ]^O_

Ciu-sim₀-refl : (f : CBV) → Set
Ciu-sim₀-refl f = ∀ {τ} E → ciu-sim₀ {f} {τ} E E
ciu-sim₀-refl : ∀ {f} → Ciu-sim₀-refl f
ciu-sim₀-refl {f} = case f return Ciu-sim₀-refl of
  λ { `val → prfV ; `trm → prfT }
  where
    prfV : Ciu-sim₀-refl `val
    prfT : Ciu-sim₀-refl `trm

    prfV {`b β} (`var ())
    prfV {`b β} (`b b) = ciu-sim₀^V-b (ciu-sim₀^B-b (sim₀^B-b b))
    prfV {σ `→ τ₁} (`var ())
    prfV {σ `→ τ} (`λ M) = ciu-sim₀^V-λ (λ U → prfT (M ⟨ U /var₀⟩))

    -- NB: sim₀-refl used for relating final values!
    prfT {τ} M {σ} {S} = lemma-[ sim₀-refl ]^F-refl S M

lemma-2-6O-frm : ∀ {Γ} {τ} {M N} → cxt-sim M N → ciu-sim {`trm} {Γ} {τ} M N
lemma-2-6O-frm {M = M} {N = N} sMN ρ {σ} {S} evSM
  with sMN (letF-cxt S ⟪- ρ -⟫)
... | prf rewrite letF-⟪ M ⟫ S ⟪- ρ -⟫ with prf (lemmaF evSM)
... | V , derSN , sUV rewrite letF-⟪ N ⟫ S ⟪- ρ -⟫ =
  V , corollaryF derSN , sUV

lemma-2-6-frm : ∀ {τ} {M N} → cxt-sim₀ M N → ciu-sim₀ {`trm} {τ} M N
lemma-2-6-frm {τ} {M} {N} sMN {σ} {S}
  with lemma-2-6O-frm {ε} {τ} {M} {N} sMN `ε {σ} {S}
... | prf rewrite ι^Env₀-lemma `ε M | ι^Env₀-lemma `ε N = prf

{--------------------------------}
{-- Logical frame approximation -}
{--------------------------------}

log-frm-sim₀^V : GRel₀^V
log-frm-sim₀^T : GRel₀^T

frm-sim₀ : {σ τ : Ty} → Rel^S {L.zero} {σ} {τ}
frm-sim₀ {σ} {τ} S^U S^V = ∀ {U V} → log-frm-sim₀^V {τ} U V →
  S^U , `val U [ sim₀ ]^F S^V , `val V

log-frm-sim₀ : GRel₀^E
log-frm-sim₀ = λ { {`val} → log-frm-sim₀^V ; {`trm} → log-frm-sim₀^T }

log-frm-sim₀^V {`b β} (`var ())
log-frm-sim₀^V {`b β} (`b b) (`var ())
log-frm-sim₀^V {`b β} (`b b) (`b b') = sim₀^B b b'
log-frm-sim₀^V {σ `→ τ} (`var ())
log-frm-sim₀^V {σ `→ τ} (`λ M) (`var ())
log-frm-sim₀^V {σ `→ τ} (`λ M) (`λ N) =
  ∀ {U V} → log-frm-sim₀^V U V → log-frm-sim₀^T (M ⟨ U /var₀⟩) (N ⟨ V /var₀⟩)

log-frm-sim₀^T {τ} M N = ∀ {σ} → M [ frm-sim₀ {σ} {τ} & sim₀^V {σ} ]^F N

log-frm-sim : ∀ {f} {Γ} {τ} → Rel^E {f} {_} {Γ} {τ}
log-frm-sim = _O^[ log-frm-sim₀ ]^O_

Log-frm-sim-sim₀ : (f : CBV) → Set
Log-frm-sim-sim₀ f = ∀ {σ} {M N} → log-frm-sim₀ M N → sim₀ {f} {σ} M N
log-frm-sim-sim₀ : ∀ {f} → Log-frm-sim-sim₀ f
log-frm-sim-sim₀ {f} = case f return Log-frm-sim-sim₀ of
  λ { `val → prfV ; `trm → prfT }
    where
      prfV : Log-frm-sim-sim₀ `val
      prfT : Log-frm-sim-sim₀ `trm

      frm-sim₀-id-refl : ∀ {σ} → frm-sim₀ {σ} {σ} Id Id
      frm-sim₀-id-refl _ (↓red () evIdU)
      frm-sim₀-id-refl {U = U} {V = V} sUV ↓val = V , ↓val , prfV sUV

      prfV {`b β} {`var ()}
      prfV {`b β} {`b b} {`var ()}
      prfV {`b β} {`b b} {`b b'} sBB' = sim₀^V-b sBB'
      prfV {σ `→ τ} {`var ()}
      prfV {σ `→ τ} {`λ M} {`var ()}
      prfV {σ `→ τ} {`λ M} {`λ N} _ = sim₀^V-λ

      prfT {τ} {M} {N} sMN derM with sMN {τ} frm-sim₀-id-refl (corollary derM)
      ... | V , evIdN , sUV = V , lemmaF evIdN , sUV

Log-frm-sim₀-log-frm-sim : (f : CBV) → Set
Log-frm-sim₀-log-frm-sim f = ∀ {σ} {M N} → log-frm-sim₀ M N →
  log-frm-sim {f} {ε} {σ} M N

log-frm-sim₀-log-frm-sim : ∀ {f} → Log-frm-sim₀-log-frm-sim f
log-frm-sim₀-log-frm-sim {f} = case f return Log-frm-sim₀-log-frm-sim of
  λ { `val → prfV ; `trm → prfT }
 where
  prfV : Log-frm-sim₀-log-frm-sim `val
  prfT : Log-frm-sim₀-log-frm-sim `trm
  prfV {σ} {V} {W} sVW {ρV} {ρW} simρ
    rewrite ι^Env₀-lemma ρV V | ι^Env₀-lemma ρW W = sVW
  prfT {σ} {M} {N} sMN {ρM} {ρN} simρ
    rewrite ι^Env₀-lemma ρM M | ι^Env₀-lemma ρN N = sMN


-- properties of frame stack evaluation

lemma-2-10i-stk : {ℓ : Level} {σ τ : Ty} {R^V : GRel^V {ℓ} {σ}}
  {R^S : Rel^S {ℓ} {σ} {τ}} {M N P : Trm₀ τ} →
  M →₁ P → M [ R^S & R^V ]^F N → P [ R^S & R^V ]^F N
lemma-2-10i-stk red r sSPN evSP with ↓red red evSP
... | evSM = r sSPN evSM

lemma-2-10i-exp-stk : {ℓ : Level} {σ τ : Ty}
  {R^V : GRel^V {ℓ} {σ}} {R^S : Rel^S {ℓ} {σ} {τ}}
  {M N P : Trm₀ τ} → M →₁ P → (P [ R^S & R^V ]^F N) → M [ R^S & R^V ]^F N
lemma-2-10i-exp-stk red r sSMN evSM with ↓standard evSM
... | V , evIdM , evSV with lemma-2-3i (lemmaF evIdM) red
... | derP = r sSMN (↓letV-lemma derP evSV)

lemma-2-10ii-stk : {ℓ : Level} {σ τ : Ty}
  {R^V : GRel^V {ℓ} {σ}} {R^S : Rel^S {ℓ} {σ} {τ}}
  {M N P : Trm₀ τ} → N →₁ P → (M [ R^S & R^V ]^F N) → M [ R^S & R^V ]^F P
lemma-2-10ii-stk red r sSMP evSM with r sSMP evSM
... | V , evTN , rUV with ↓standard evTN
... | W , evIdN , evTW with lemma-2-3i (lemmaF evIdN) red
... | derP = V , ↓letV-lemma derP evTW , rUV

lemma-2-10ii-exp-stk : {ℓ : Level} {σ τ : Ty}
  {R^V : GRel^V {ℓ} {σ}} {R^S : Rel^S {ℓ} {σ} {τ}}
  {M N P : Trm₀ τ} → N →₁ P → (M [ R^S & R^V ]^F P) → M [ R^S & R^V ]^F N
lemma-2-10ii-exp-stk red r sSMN evSM with r sSMN evSM
... | V , evTP , rUV with ↓red red evTP
... | evTN = V , evTN , rUV

-- Compatibility lemmas: frame stack evaluation closed under the term
-- constructors.

lemma-[-]^F-app : {ℓ : Level} {ω : Ty} {R^V : {τ : Ty} → GRel^V {ℓ} {τ}}
  {R^S : {τ : Ty} → Rel^S {ℓ} {ω} {τ}} → ∀ {σ τ} →
  (R^V-λ : ∀ {M N} {V W} → R^V {σ} V W → R^V {σ `→ τ} (`λ M) (`λ N) →
    M ⟨ V /var₀⟩ [ R^S {τ} & R^V {ω} ]^F N ⟨ W /var₀⟩) →
 ∀ {f g} {a b} → R^V {σ `→ τ} f g → R^V {σ} a b →
   (f `$ a) [ R^S {τ} & R^V {ω} ]^F (g `$ b)
lemma-[-]^F-app R^V-λ {`var ()}
lemma-[-]^F-app R^V-λ {`λ M} {`var ()}
lemma-[-]^F-app R^V-λ {`λ M} {`λ N} {V} {W} rMN rVW =
  lemma-2-10i-exp-stk →₁app (lemma-2-10ii-exp-stk →₁app (R^V-λ rVW rMN))

beta-stk-if : ∀ {σ τ ω} {S : Frm σ τ} {M : (ω ⊢ Trm τ) ε}
  {U : Val₀ ω} {V : Val₀ σ} → S , M ⟨ U /var₀⟩ ↓ V → S , `λ M `$ U ↓ V
beta-stk-if evSMU with ↓standard evSMU
... | W , evIdMU , evSW with lemmaF evIdMU
... | derMW = ↓letV-lemma (⇓app derMW) evSW

beta-stk-only-if : ∀ {σ τ ω} {S : Frm σ τ} {M : (ω ⊢ Trm τ) ε}
  {U : Val₀ ω} {V : Val₀ σ} → S , `λ M `$ U ↓ V → S , M ⟨ U /var₀⟩ ↓ V
beta-stk-only-if evSMU with ↓standard evSMU
... | W , evIdMU , evSW with lemmaF evIdMU
... | ⇓app derMW = ↓letV-lemma derMW evSW

-- Not as slick as James' proof using lemma-[-]^T-app!
log-frm-sim₀^T-app : ∀ {σ τ} {f g} {a b} → log-frm-sim₀^V {σ `→ τ} f g →
  log-frm-sim₀ a b → log-frm-sim₀ (f `$ a) (g `$ b)
log-frm-sim₀^T-app {f = `var ()}
log-frm-sim₀^T-app {f = `λ M} {`var ()} sFG sAB sST evS
log-frm-sim₀^T-app {f = `λ M} {g = `λ N} {a = U} {b = V} sFG sAB sST evS
   with sFG sAB sST (beta-stk-only-if evS)
... | U^T , evTNV , sU^SU^T = U^T , beta-stk-if evTNV , sU^SU^T

log-frm-sim₀^T-if : ∀ {σ} {b b'} {l l' r r'} → log-frm-sim₀ b b' →
  log-frm-sim₀ l l' → log-frm-sim₀ r r' →
  log-frm-sim₀^T {σ} (`if b l r) (`if b' l' r')
log-frm-sim₀^T-if {b = `var ()}
log-frm-sim₀^T-if {b = `b b} {`var ()}
log-frm-sim₀^T-if {b = `b ff} {`b tt} ()
log-frm-sim₀^T-if {b = `b tt} {`b ff} ()
log-frm-sim₀^T-if {b = `b ff} {`b ff} _ _ sRR' =
  lemma-2-10i-exp-stk →₁if (lemma-2-10ii-exp-stk →₁if sRR')
log-frm-sim₀^T-if {b = `b tt} {`b tt} _ sLL' _ =
  lemma-2-10ii-exp-stk →₁if (lemma-2-10i-exp-stk →₁if sLL')

frm-sim₀-ext : ∀ {σ τ ω} {S T : Frm σ τ} {N N'} → frm-sim₀ {σ} {τ} S T →
  (∀ {V W : Val₀ ω} → log-frm-sim₀ V W →
    log-frm-sim₀ (N ⟨ V /var₀⟩) (N' ⟨ W /var₀⟩)) → frm-sim₀ (S ∙ N) (T ∙ N')
frm-sim₀-ext sST sCC' sVW (↓red () evSNV)
frm-sim₀-ext sST sCC' sVW (↓letV evSNV) with sCC' sVW sST evSNV
... | W , evTNV , simRes = W , ↓letV evTNV , simRes

log-frm-sim₀^T-let : ∀ {σ τ} {M M'} {N N'} → (log-frm-sim₀^T {σ} M M') →
  (∀ {V W} → log-frm-sim₀ V W →
    log-frm-sim₀ (N ⟨ V /var₀⟩) (N' ⟨ W /var₀⟩)) →
  log-frm-sim₀^T {τ} (`let M N) (`let M' N')
log-frm-sim₀^T-let sMM' sCC' sST (↓red () evSMN)
log-frm-sim₀^T-let {σ} {τ} {M = M} {M'} {N} {N'}
                   sMM' sCC' {ω} {S} {T} sST (↓letT evSNM)
  with frm-sim₀-ext {N = N} {N' = N'} sST sCC'
... | sSTN with sMM' {ω} sSTN evSNM
... | W , evTNW , sVW = W , ↓letT evTNW , sVW

log-frm-sim₀^Ext : ∀ {σ} {V W : Val₀ σ} {Γ} {ρ ρ' : Env₀ Γ}
  (simρ : ρ [ log-frm-sim₀^V ]^Env ρ')
  (sVW : log-frm-sim₀ V W) →
  (ρ `∙ V) [ log-frm-sim₀^V ]^Env (ρ' `∙ W)
log-frm-sim₀^Ext simρ sVW = _∙₀^R_ {𝓔^R = log-frm-sim₀^V} simρ sVW

-- Essentially a copy of lemma-2-16 from James' development.
log-frm-sim-refl : ∀ {f} {Γ} {τ} (E : Exp {f} τ Γ) → log-frm-sim E E
log-frm-sim-refl (`var x) simρ = simρ x
log-frm-sim-refl (`b b) simρ = sim₀^B-b b
log-frm-sim-refl (`λ M) {ρM} {ρM'} simρ {U} {V} sUV
  with log-frm-sim-refl M {ρM `∙ U} {ρM' `∙ V} (log-frm-sim₀^Ext simρ sUV)
... | prf rewrite lemma34 M ρM U | lemma34 M ρM' V = prf
log-frm-sim-refl (`val V) {ρS} {ρT} simρ with log-frm-sim-refl V simρ
... | sVV = λ {σ} {S} {T} sST evSV → sST sVV evSV
log-frm-sim-refl (f `$ a) simρ = log-frm-sim₀^T-app F A
  where F = log-frm-sim-refl f simρ
        A = log-frm-sim-refl a simρ
log-frm-sim-refl (`if b l r) simρ = log-frm-sim₀^T-if B L R
  where B = log-frm-sim-refl b simρ
        L = log-frm-sim-refl l simρ
        R = log-frm-sim-refl r simρ
log-frm-sim-refl (`let M N) {ρ} {ρ'} simρ with log-frm-sim-refl M simρ
... | prfM = log-frm-sim₀^T-let prfM prfN
  where Nρ = subst N (ext₀^Env ρ)
        Nρ' = subst N (ext₀^Env ρ')
        prfN : ∀ {V W} → log-frm-sim₀ V W →
               log-frm-sim₀ (Nρ ⟨ V /var₀⟩) (Nρ' ⟨ W /var₀⟩)
        prfN {V} {W} sVW with log-frm-sim-refl N {ρ `∙ V} {ρ' `∙ W}
                                               (log-frm-sim₀^Ext simρ sVW)
        ... | prf rewrite lemma34 N ρ V | lemma34 N ρ' W = prf

Log-frm-sim₀-refl : (f : CBV) → Set
Log-frm-sim₀-refl f = ∀ {τ} E → log-frm-sim₀ {f} {τ} E E
log-frm-sim₀-refl : ∀ {f} → Log-frm-sim₀-refl f
log-frm-sim₀-refl {f} = case f return Log-frm-sim₀-refl of
  λ { `val → prfV ; `trm → prfT }
  where
    prfV : Log-frm-sim₀-refl `val
    prfT : Log-frm-sim₀-refl `trm
    prfS : ∀ {σ τ} S → frm-sim₀ {σ} {τ} S S

    prfV {`b β} (`var ())
    prfV {`b β} (`b b) = sim₀^B-b b
    prfV {σ `→ τ} (`var ())
    prfV {σ `→ τ} (`λ M) sUV =
      log-frm-sim-refl M (Val₀→Env₀ {𝓔^R = log-frm-sim₀^V} sUV)

    prfT {τ} M sS^MS^N evalSM with ↓standard evalSM
    ... | U , evalIdM , evalS^MU with sS^MS^N (prfV U) evalS^MU
    ... | W^V , evalS^NU , sW^UW^V =
      W^V , ↓letV-lemma (lemmaF evalIdM) evalS^NU , sW^UW^V

    prfS Id {U} {V} sUV ↓val = V , ↓val , log-frm-sim-sim₀ {`val} sUV
    prfS Id sUV (↓red () evS)
    prfS (S ∙ N) rUV (↓red () derU)
    prfS (S ∙ N) {U = U} rUV (↓letV derU) with prfS S
    ... | iH with (prfT (N ⟨ U /var₀⟩)) iH derU
    ... | W^V , derV , rW^UW^V = W^V , ↓letV derV , rW^UW^V

lemma-2-18-aux-frm : ∀ {f} {Γ Δ} {τ υ} (P : Cxt⟪ Γ ⊢ τ ⟫ {f} υ Δ) →
 ∀ {M N} → log-frm-sim M N → log-frm-sim (P ⟪ M ⟫) (P ⟪ N ⟫)
lemma-2-18-aux-frm (`λ P) {M} {N} sMN {ρM} {ρN} simρ {U} {V} sUV
  with lemma-2-18-aux-frm P {M} {N} sMN {ρM `∙ U} {ρN `∙ V}
       (log-frm-sim₀^Ext simρ sUV)
... | prf rewrite lemma34 (P ⟪ M ⟫) ρM U | lemma34 (P ⟪ N ⟫) ρN V = prf
lemma-2-18-aux-frm (`exp E) sMN simρ = log-frm-sim-refl E simρ

lemma-2-18-aux-frm ⟪- ρ -⟫ {M} {N} sMN {ρM} {ρN} simρ
  with sMN {ρM *-Sub ρ} {ρN *-Sub ρ}
       (λ {σ} v → log-frm-sim-refl (var ρ {σ} v) simρ)
... | prf rewrite lemma33 ρM ρ M | lemma33 ρN ρ N = prf

lemma-2-18-aux-frm (`val P) {M} {N} sMN {ρM} {ρN} simρ
  with lemma-2-18-aux-frm P sMN simρ
... | prf = λ sST → sST prf -- This looks dodgy but Agda doesn't like
                            -- introducing sST before the with clause!

lemma-2-18-aux-frm (F `$ A) sMN simρ =
  log-frm-sim₀^T-app (lemma-2-18-aux-frm F sMN simρ)
                     (lemma-2-18-aux-frm A sMN simρ)
lemma-2-18-aux-frm (`if B L R) sMN simρ = log-frm-sim₀^T-if prfB prfL prfR
  where prfB = lemma-2-18-aux-frm B sMN simρ
        prfL = lemma-2-18-aux-frm L sMN simρ
        prfR = lemma-2-18-aux-frm R sMN simρ
lemma-2-18-aux-frm (`let P Q) {M} {N} sMN {ρM} {ρN} simρ =
  log-frm-sim₀^T-let (lemma-2-18-aux-frm P sMN simρ) prfQ
  where
    QM = subst (Q ⟪ M ⟫) (ext₀^Env ρM)

    QN = subst (Q ⟪ N ⟫) (ext₀^Env ρN)

    prfQ : ∀ {V W} → log-frm-sim₀ V W →
      log-frm-sim₀ (QM ⟨ V /var₀⟩) (QN ⟨ W /var₀⟩)
    prfQ {V} {W} sVW with lemma-2-18-aux-frm Q {M} {N} sMN {ρM `∙ V} {ρN `∙ W}
                                             (log-frm-sim₀^Ext simρ sVW)
    ... | prf rewrite lemma34 (Q ⟪ M ⟫) ρM V | lemma34 (Q ⟪ N ⟫) ρN W = prf

-- Proof follows James' approach to the letter!
lemma-2-18O-frm : ∀ {Γ} {τ} {M N} → log-frm-sim M N →
  cxt-sim {`trm} {Γ} {τ} M N
lemma-2-18O-frm {Γ} {τ} {M} {N} sMN P
  with lemma-2-18-aux-frm P {M} {N} sMN ([ log-frm-sim₀^V ]^Env-refl₀ ι^Env)
... | prf = log-frm-sim-sim₀ {`trm} sPMN
 where
  sPMN : log-frm-sim₀^T (P ⟪ M ⟫) (P ⟪ N ⟫)
  sPMN rewrite PEq.sym (ι^Env₀ (P ⟪ M ⟫)) | PEq.sym (ι^Env₀ (P ⟪ N ⟫)) = prf

log-frm-sim₀-lift : ∀ {σ} {V W} → log-frm-sim₀^V {σ} V W →
                    log-frm-sim₀ (`val V) (`val W)
log-frm-sim₀-lift {V = V} {W = W} sVW {τ} {S} {T} sST evSV = sST sVW evSV

Lemma-2-18-frm : (f : CBV) → Set
Lemma-2-18-frm f = ∀ {τ} {M N} → log-frm-sim₀ M N → cxt-sim₀ {f} {τ} M N
lemma-2-18-frm : ∀ {f} → Lemma-2-18-frm f
lemma-2-18-frm {f} = case f return Lemma-2-18-frm of
  λ { `val → prfV ; `trm → prfT }
 where
  prfV : Lemma-2-18-frm `val
  prfT : Lemma-2-18-frm `trm
  prfV {M = V} {N = W} = prfT ∘ log-frm-sim₀-lift
  prfT = lemma-2-18O-frm ∘ (log-frm-sim₀-log-frm-sim {`trm})

Lemma-2-20-aux-frm : (f : CBV) → Set
Lemma-2-20-aux-frm f = ∀ {τ} {M N P} → ciu-sim₀ M N → log-frm-sim₀ N P →
                   log-frm-sim₀ {f} {τ} M P
lemma-2-20-aux-frm : ∀ {f} → Lemma-2-20-aux-frm f
lemma-2-20-aux-frm {f} = case f return Lemma-2-20-aux-frm of
  λ { `val →  prfV ; `trm → prfT  }
 where
  prfV : Lemma-2-20-aux-frm `val
  prfT : Lemma-2-20-aux-frm `trm
  prfV {`b β} {`var ()}
  prfV {`b β} {`b b} (ciu-sim₀^V-b _) r = r
  prfV {σ `→ τ} {`var ()}
  prfV {σ `→ τ} {`λ M} {P = `var ()}
  prfV {σ `→ τ} {`λ M} {P = `λ P} (ciu-sim₀^V-λ sMN) r {U} {V} sUV =
    prfT (sMN U) (r sUV)

  prfT {τ} {M} {N} {P} sMN sNP {σ} {S} sST evSM with sMN evSM
  ... | V , evSN , sUV with sNP sST evSN
  ... | W , evTP , sVW = W , evTP , sim₀-trans {`val} sUV sVW

lemma-2-20-frm : ∀ {f} {τ} {M N} → ciu-sim₀ M N → log-frm-sim₀ {f} {τ} M N
lemma-2-20-frm {f} {τ} {M} {N} sMN =
  lemma-2-20-aux-frm {f} {τ} sMN (log-frm-sim₀-refl N)

lemma-2-20O-frm : ∀ {Γ} {τ} {M N : Trm τ Γ} → ciu-sim M N → log-frm-sim M N
lemma-2-20O-frm {Γ} {τ} {M} {N} sMN {ρM} {ρN} simρ =
  lemma-2-20-aux-frm {`trm} (sMN ρM) (log-frm-sim-refl N simρ)

-- Reminiscent of Howe's property: if e1 R^H e2 and e2 R e3 then e1 R^H e3.
Howe-property : (f : CBV) → Set
Howe-property f = ∀ {τ} {M N P} → log-frm-sim₀ M N → ciu-sim₀ N P →
                  log-frm-sim₀ {f} {τ} M P
howe-property : ∀ {f} → Howe-property f
howe-property {f} = case f return Howe-property of
  λ { `val →  prfV ; `trm → prfT  }
 where
  prfV : Howe-property `val
  prfT : Howe-property `trm

  prfV {`b β} {`var ()}
  prfV {`b β} {`b b} {`var ()}
  prfV {`b β} {`b b} {`b b'} l (ciu-sim₀^V-b _) = l
  prfV {σ `→ τ} {`var ()}
  prfV {σ `→ τ} {M = `λ M} {`var ()}
  prfV {σ `→ τ} {M = `λ M} {N = `λ N} sMN (ciu-sim₀^V-λ sNP) {U} {V} sUV =
    prfT (sMN sUV) (sNP U)

  prfT {τ} {M} {N} {P} sMN sNP {σ} {S} sST evSM with sMN sST evSM
  ... | V , evSN , sUV with sNP evSN
  ... | W , evTP , sVW = W , evTP , sim₀-trans {`val} sUV sVW

{------------}
{-- Summary -}
{------------}

-- on closed terms

cxt-sim₀→ciu-sim₀^T : ∀ {τ} {M N : Trm₀ τ} → cxt-sim₀ M N → ciu-sim₀ M N
cxt-sim₀→ciu-sim₀^T = lemma-2-6-frm

ciu-sim₀→log-frm-sim₀^T : ∀ {τ} {M N : Trm₀ τ} →
  ciu-sim₀ M N → log-frm-sim₀ M N
ciu-sim₀→log-frm-sim₀^T = lemma-2-20-frm {`trm}

log-frm-sim₀→cxt-sim₀^T : ∀ {τ} {M N : Trm₀ τ} →
  log-frm-sim₀ M N → cxt-sim₀ M N
log-frm-sim₀→cxt-sim₀^T = lemma-2-18-frm {`trm}

-- on open terms

cxt-sim→ciu-sim^T : ∀ {Γ} {τ} {M N : Trm τ Γ} → cxt-sim M N → ciu-sim M N
cxt-sim→ciu-sim^T = lemma-2-6O-frm

ciu-sim→log-frm-sim^T : ∀ {Γ} {τ} {M N : Trm τ Γ} →
  ciu-sim M N → log-frm-sim M N
ciu-sim→log-frm-sim^T {Γ} {τ} {M} {N} = lemma-2-20O-frm {Γ} {τ} {M} {N}

log-frm-sim→cxt-sim^T : ∀ {Γ} {τ} {M N : Trm τ Γ} →
  log-frm-sim M N → cxt-sim M N
log-frm-sim→cxt-sim^T = lemma-2-18O-frm
