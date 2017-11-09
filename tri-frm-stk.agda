{--------------------------------}
{-- Triangle for frame stacks. --}
{--------------------------------}
module tri-frm-stk where

open import Level as L using (Level ; _⊔_)
open import Function as F hiding (_∋_ ; _$_)

open import acmm
open import sim-fusion-lemmas
open import relations
open import big-step-prop
open import obs-apx
open import ciu-apx
open import frm-stk-prop

-- Lemma regarding Val to <Frm,Trm> configuration relation transformer
lemma-[_]^F-refl : {ℓ^V : Level} {σ τ : Ty} {R : GRel^V {ℓ^V} {σ}}
  (r : (V : Val₀ σ) → R V V) → (S : Frm σ τ) → (M : Trm₀ τ) →
  S , M [ R ]^F S , M
lemma-[ r ]^F-refl S M {U = U} der = U , der , r U

-- Now prove directly that CIU approximation implies `applicative frame stack'
-- approximation

mutual

  app-frm-apx₀ : GRel₀^E
  app-frm-apx₀ {`val} = app-frm-apx₀^V
  app-frm-apx₀ {`trm} = app-frm-apx₀^T

  data app-frm-apx₀^B : GRel₀^B where
    app-frm-apx₀^B-b : ∀ {β} {b b'} →
      gnd-eqv₀^B {β} b b' → app-frm-apx₀^B {β} b b'

  data app-frm-apx₀^V : GRel₀^V where
    app-frm-apx₀^V-b : ∀ {β} {b b'} → app-frm-apx₀^B {β} b b' →
      app-frm-apx₀^V {`b β} (`b b) (`b b)

    app-frm-apx₀^V-λ : ∀ {σ τ} {M N} →
      (∀ U → app-frm-apx₀^T {τ} (M ⟨ U /var₀⟩) (N ⟨ U /var₀⟩)) →
      app-frm-apx₀^V {σ `→ τ} (`λ M) (`λ N)

  app-frm-apx₀^T : GRel₀^T
  app-frm-apx₀^T {τ} M N = ∀ {σ} {S} → S , M [ gnd-eqv₀^V {σ} ]^F S , N

App-frm-apx : ∀ (f : CBV) → Set₁
App-frm-apx f = ∀ {Γ} {τ} → Rel^E {f} {L.zero} {Γ} {τ}
app-frm-apx : ∀ {f} → App-frm-apx f
app-frm-apx {f} = case f return App-frm-apx of
  λ { `val →  apxV ; `trm → apxT  }
 where
  apxV : App-frm-apx `val
  apxT : App-frm-apx `trm
  apxV {Γ} {τ} = _[ apxT {Γ} {τ} ]^V_
  apxT {Γ} {τ} = _[ app-frm-apx₀ {`trm} {τ} ]^O_

App-frm-apx₀-refl : (f : CBV) → Set
App-frm-apx₀-refl f = ∀ {τ} E → app-frm-apx₀ {f} {τ} E E
app-frm-apx₀-refl : ∀ {f} → App-frm-apx₀-refl f
app-frm-apx₀-refl {f} = case f return App-frm-apx₀-refl of
  λ { `val → prfV ; `trm → prfT }
  where
    prfV : App-frm-apx₀-refl `val
    prfT : App-frm-apx₀-refl `trm

    prfV {`b β} (`var ())
    prfV {`b β} (`b b) = app-frm-apx₀^V-b (app-frm-apx₀^B-b (gnd-eqv₀^B-b b))
    prfV {σ `→ τ₁} (`var ())
    prfV {σ `→ τ} (`λ M) = app-frm-apx₀^V-λ (λ U → prfT (M ⟨ U /var₀⟩))

    -- NB: gnd-eqv₀-refl used for relating final values!
    prfT {τ} M {σ} {S} = lemma-[ gnd-eqv₀-refl ]^F-refl S M

ciu-apx→app-frm-apx : ∀ {Γ} {τ} {M N} →
  ciu-apx M N → app-frm-apx {`trm} {Γ} {τ} M N
ciu-apx→app-frm-apx {M = M} {N = N} sMN ρ {σ} {S} evSM
  with sMN (letF-ciu S ⟪- ρ -⟫)
... | prf rewrite letF-⟪ M ⟫ S ⟪- ρ -⟫ with prf (lemmaF evSM)
... | V , derSN , sUV rewrite letF-⟪ N ⟫ S ⟪- ρ -⟫ =
  V , corollaryF derSN , sUV

ciu-apx₀→app-frm-apx₀ : ∀ {τ} {M N} →
  ciu-apx₀ M N → app-frm-apx₀ {`trm} {τ} M N
ciu-apx₀→app-frm-apx₀ {τ} {M} {N} sMN {σ} {S}
  with ciu-apx→app-frm-apx {ε} {τ} {M} {N} sMN `ε {σ} {S}
... | prf rewrite ι^Env₀-lemma `ε M | ι^Env₀-lemma `ε N = prf

{--------------------------------}
{-- Logical frame approximation -}
{--------------------------------}

log-frm-apx₀^V : GRel₀^V
log-frm-apx₀^T : GRel₀^T

frm-apx₀ : {σ τ : Ty} → Rel^S {L.zero} {σ} {τ}
frm-apx₀ {σ} {τ} S^U S^V = ∀ {U V} → log-frm-apx₀^V {τ} U V →
  S^U , `val U [ gnd-eqv₀ ]^F S^V , `val V

log-frm-apx₀ : GRel₀^E
log-frm-apx₀ {`val} = log-frm-apx₀^V
log-frm-apx₀ {`trm} = log-frm-apx₀^T

log-frm-apx₀^V {`b β} (`var ())
log-frm-apx₀^V {`b β} (`b b) (`var ())
log-frm-apx₀^V {`b β} (`b b) (`b b') = gnd-eqv₀^B b b'
log-frm-apx₀^V {σ `→ τ} (`var ())
log-frm-apx₀^V {σ `→ τ} (`λ M) (`var ())
log-frm-apx₀^V {σ `→ τ} (`λ M) (`λ N) =
  ∀ {U V} → log-frm-apx₀^V U V → log-frm-apx₀^T (M ⟨ U /var₀⟩) (N ⟨ V /var₀⟩)

log-frm-apx₀^T {τ} M N = ∀ {σ} → M [ frm-apx₀ {σ} {τ} & gnd-eqv₀^V {σ} ]^F N

log-frm-apx : ∀ {f} {Γ} {τ} → Rel^E {f} {_} {Γ} {τ}
log-frm-apx = _O^[ log-frm-apx₀ ]^O_

Log-frm-apx-gnd-eqv₀ : (f : CBV) → Set
Log-frm-apx-gnd-eqv₀ f = ∀ {σ} {M N} → log-frm-apx₀ M N → gnd-eqv₀ {f} {σ} M N
log-frm-apx-gnd-eqv₀ : ∀ {f} → Log-frm-apx-gnd-eqv₀ f
log-frm-apx-gnd-eqv₀ {f} = case f return Log-frm-apx-gnd-eqv₀ of
  λ { `val → prfV ; `trm → prfT }
    where
      prfV : Log-frm-apx-gnd-eqv₀ `val
      prfT : Log-frm-apx-gnd-eqv₀ `trm

      frm-apx₀-id-refl : ∀ {σ} → frm-apx₀ {σ} {σ} Id Id
      frm-apx₀-id-refl _ (↓red () evIdU)
      frm-apx₀-id-refl {U = U} {V = V} sUV ↓val = V , ↓val , prfV sUV

      prfV {`b β} {`var ()}
      prfV {`b β} {`b b} {`var ()}
      prfV {`b β} {`b b} {`b b'} sBB' = gnd-eqv₀^V-b sBB'
      prfV {σ `→ τ} {`var ()}
      prfV {σ `→ τ} {`λ M} {`var ()}
      prfV {σ `→ τ} {`λ M} {`λ N} _ = gnd-eqv₀^V-λ

      prfT {τ} {M} {N} sMN derM with sMN {τ} frm-apx₀-id-refl (corollary derM)
      ... | V , evIdN , sUV = V , lemmaF evIdN , sUV

Log-frm-apx₀-log-frm-apx : (f : CBV) → Set
Log-frm-apx₀-log-frm-apx f = ∀ {σ} {M N} → log-frm-apx₀ M N →
  log-frm-apx {f} {ε} {σ} M N

log-frm-apx₀-log-frm-apx : ∀ {f} → Log-frm-apx₀-log-frm-apx f
log-frm-apx₀-log-frm-apx {f} = case f return Log-frm-apx₀-log-frm-apx of
  λ { `val → prfV ; `trm → prfT }
 where
  prfV : Log-frm-apx₀-log-frm-apx `val
  prfT : Log-frm-apx₀-log-frm-apx `trm
  prfV {σ} {V} {W} sVW {ρV} {ρW} apxρ
    rewrite ι^Env₀-lemma ρV V | ι^Env₀-lemma ρW W = sVW
  prfT {σ} {M} {N} sMN {ρM} {ρN} apxρ
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
beta-stk-if evSMU = ↓red →₁app evSMU

beta-stk-only-if : ∀ {σ τ ω} {S : Frm σ τ} {M : (ω ⊢ Trm τ) ε}
  {U : Val₀ ω} {V : Val₀ σ} → S , `λ M `$ U ↓ V → S , M ⟨ U /var₀⟩ ↓ V
beta-stk-only-if (↓red →₁app evSMU) = evSMU

-- Not as slick as James' proof using lemma-[-]^T-app!
log-frm-apx₀^T-app : ∀ {σ τ} {f g} {a b} → log-frm-apx₀^V {σ `→ τ} f g →
  log-frm-apx₀ a b → log-frm-apx₀ (f `$ a) (g `$ b)
log-frm-apx₀^T-app {f = `var ()}
log-frm-apx₀^T-app {f = `λ M} {`var ()} sFG sAB sST evS
log-frm-apx₀^T-app {f = `λ M} {g = `λ N} {a = U} {b = V} sFG sAB sST evS
   with sFG sAB sST (beta-stk-only-if evS)
... | U^T , evTNV , sU^SU^T = U^T , beta-stk-if evTNV , sU^SU^T

log-frm-apx₀^T-if : ∀ {σ} {b b'} {l l' r r'} → log-frm-apx₀ b b' →
  log-frm-apx₀ l l' → log-frm-apx₀ r r' →
  log-frm-apx₀^T {σ} (`if b l r) (`if b' l' r')
log-frm-apx₀^T-if {b = `var ()}
log-frm-apx₀^T-if {b = `b b} {`var ()}
log-frm-apx₀^T-if {b = `b ff} {`b tt} ()
log-frm-apx₀^T-if {b = `b tt} {`b ff} ()
log-frm-apx₀^T-if {b = `b ff} {`b ff} _ _ sRR' =
  lemma-2-10i-exp-stk →₁if (lemma-2-10ii-exp-stk →₁if sRR')
log-frm-apx₀^T-if {b = `b tt} {`b tt} _ sLL' _ =
  lemma-2-10ii-exp-stk →₁if (lemma-2-10i-exp-stk →₁if sLL')

frm-apx₀-ext : ∀ {σ τ ω} {S T : Frm σ τ} {N N'} → frm-apx₀ {σ} {τ} S T →
  (∀ {V W : Val₀ ω} → log-frm-apx₀ V W →
    log-frm-apx₀ (N ⟨ V /var₀⟩) (N' ⟨ W /var₀⟩)) → frm-apx₀ (S ∙ N) (T ∙ N')
frm-apx₀-ext sST sCC' sVW (↓red () evSNV)
frm-apx₀-ext sST sCC' sVW (↓letV evSNV) with sCC' sVW sST evSNV
... | W , evTNV , apxRes = W , ↓letV evTNV , apxRes

log-frm-apx₀^T-let : ∀ {σ τ} {M M'} {N N'} → (log-frm-apx₀^T {σ} M M') →
  (∀ {V W} → log-frm-apx₀ V W →
    log-frm-apx₀ (N ⟨ V /var₀⟩) (N' ⟨ W /var₀⟩)) →
  log-frm-apx₀^T {τ} (`let M N) (`let M' N')
log-frm-apx₀^T-let sMM' sCC' sST (↓red () evSMN)
log-frm-apx₀^T-let {σ} {τ} {M = M} {M'} {N} {N'}
                   sMM' sCC' {ω} {S} {T} sST (↓letT evSNM)
  with frm-apx₀-ext {N = N} {N' = N'} sST sCC'
... | sSTN with sMM' {ω} sSTN evSNM
... | W , evTNW , sVW = W , ↓letT evTNW , sVW

log-frm-apx₀^Ext : ∀ {σ} {V W : Val₀ σ} {Γ} {ρ ρ' : Env₀ Γ}
  (apxρ : ρ [ log-frm-apx₀^V ]^Env ρ')
  (sVW : log-frm-apx₀ V W) →
  (ρ `∙ V) [ log-frm-apx₀^V ]^Env (ρ' `∙ W)
log-frm-apx₀^Ext apxρ sVW = _∙₀^R_ {𝓔^R = log-frm-apx₀^V} apxρ sVW

-- Lemma 4.13
log-frm-apx-refl : ∀ {f} {Γ} {τ} (E : Exp {f} τ Γ) → log-frm-apx E E
log-frm-apx-refl (`var x) apxρ = apxρ x
log-frm-apx-refl (`b b) apxρ = gnd-eqv₀^B-b b
log-frm-apx-refl (`λ M) {ρM} {ρM'} apxρ {U} {V} sUV
  with log-frm-apx-refl M {ρM `∙ U} {ρM' `∙ V} (log-frm-apx₀^Ext apxρ sUV)
... | prf rewrite lemma34 M ρM U | lemma34 M ρM' V = prf
log-frm-apx-refl (`val V) {ρS} {ρT} apxρ with log-frm-apx-refl V apxρ
... | sVV = λ sST evSV → sST sVV evSV
log-frm-apx-refl (f `$ a) apxρ = log-frm-apx₀^T-app F A
  where F = log-frm-apx-refl f apxρ
        A = log-frm-apx-refl a apxρ
log-frm-apx-refl (`if b l r) apxρ = log-frm-apx₀^T-if B L R
  where B = log-frm-apx-refl b apxρ
        L = log-frm-apx-refl l apxρ
        R = log-frm-apx-refl r apxρ
log-frm-apx-refl (`let M N) {ρ} {ρ'} apxρ with log-frm-apx-refl M apxρ
... | prfM = log-frm-apx₀^T-let prfM prfN
  where Nρ = subst N (ext₀^Env ρ)
        Nρ' = subst N (ext₀^Env ρ')
        prfN : ∀ {V W} → log-frm-apx₀ V W →
               log-frm-apx₀ (Nρ ⟨ V /var₀⟩) (Nρ' ⟨ W /var₀⟩)
        prfN {V} {W} sVW with log-frm-apx-refl N {ρ `∙ V} {ρ' `∙ W}
                                               (log-frm-apx₀^Ext apxρ sVW)
        ... | prf rewrite lemma34 N ρ V | lemma34 N ρ' W = prf

Log-frm-apx₀-refl : (f : CBV) → Set
Log-frm-apx₀-refl f = ∀ {τ} E → log-frm-apx₀ {f} {τ} E E
log-frm-apx₀-refl : ∀ {f} → Log-frm-apx₀-refl f
log-frm-apx₀-refl {f} = case f return Log-frm-apx₀-refl of
  λ { `val → prfV ; `trm → prfT }
  where
    prfV : Log-frm-apx₀-refl `val
    prfT : Log-frm-apx₀-refl `trm
    prfS : ∀ {σ τ} S → frm-apx₀ {σ} {τ} S S

    prfV {`b β} (`var ())
    prfV {`b β} (`b b) = gnd-eqv₀^B-b b
    prfV {σ `→ τ} (`var ())
    prfV {σ `→ τ} (`λ M) sUV =
      log-frm-apx-refl M (Val₀→Env₀ {𝓔^R = log-frm-apx₀^V} sUV)

    prfT {τ} M sS^MS^N evalSM with ↓standard evalSM
    ... | U , evalIdM , evalS^MU with sS^MS^N (prfV U) evalS^MU
    ... | W^V , evalS^NU , sW^UW^V =
      W^V , ↓letV-lemma (lemmaF evalIdM) evalS^NU , sW^UW^V

    prfS Id {U} {V} sUV ↓val = V , ↓val , log-frm-apx-gnd-eqv₀ {`val} sUV
    prfS Id sUV (↓red () evS)
    prfS (S ∙ N) rUV (↓red () derU)
    prfS (S ∙ N) {U = U} rUV (↓letV derU) with prfS S
    ... | iH with (prfT (N ⟨ U /var₀⟩)) iH derU
    ... | W^V , derV , rW^UW^V with prfV (`λ N) rUV (prfS S) derV
    ... | W , derW , rW^VW =
      W , ↓letV derW , gnd-eqv₀-trans {`val} rW^UW^V rW^VW

lemma-4-14 : ∀ {f} {Γ Δ} {τ υ} (P : VSC⟪ Γ ⊢ τ ⟫ {f} υ Δ) →
 ∀ {M N} → log-frm-apx M N → log-frm-apx (P ⟪ M ⟫) (P ⟪ N ⟫)
lemma-4-14 (`λ P) {M} {N} sMN {ρM} {ρN} apxρ {U} {V} sUV
  with lemma-4-14 P {M} {N} sMN {ρM `∙ U} {ρN `∙ V}
       (log-frm-apx₀^Ext apxρ sUV)
... | prf rewrite lemma34 (P ⟪ M ⟫) ρM U | lemma34 (P ⟪ N ⟫) ρN V = prf
lemma-4-14 (`exp E) sMN apxρ = log-frm-apx-refl E apxρ

lemma-4-14 ⟪- ρ -⟫ {M} {N} sMN {ρM} {ρN} apxρ
  with sMN {ρM *-Sub ρ} {ρN *-Sub ρ}
       (λ {σ} v → log-frm-apx-refl (var ρ {σ} v) apxρ)
... | prf rewrite lemma33 ρM ρ M | lemma33 ρN ρ N = prf

lemma-4-14 (`val P) {M} {N} sMN {ρM} {ρN} apxρ
  with lemma-4-14 P sMN apxρ
... | prf = λ sST → sST prf -- This looks dodgy but Agda doesn't like
                            -- introducing sST before the with clause!

lemma-4-14 (F `$ A) sMN apxρ =
  log-frm-apx₀^T-app (lemma-4-14 F sMN apxρ)
                     (lemma-4-14 A sMN apxρ)
lemma-4-14 (`if B L R) sMN apxρ = log-frm-apx₀^T-if prfB prfL prfR
  where prfB = lemma-4-14 B sMN apxρ
        prfL = lemma-4-14 L sMN apxρ
        prfR = lemma-4-14 R sMN apxρ
lemma-4-14 (`let P Q) {M} {N} sMN {ρM} {ρN} apxρ =
  log-frm-apx₀^T-let (lemma-4-14 P sMN apxρ) prfQ
  where
    QM = subst (Q ⟪ M ⟫) (ext₀^Env ρM)

    QN = subst (Q ⟪ N ⟫) (ext₀^Env ρN)

    prfQ : ∀ {V W} → log-frm-apx₀ V W →
      log-frm-apx₀ (QM ⟨ V /var₀⟩) (QN ⟨ W /var₀⟩)
    prfQ {V} {W} sVW with lemma-4-14 Q {M} {N} sMN {ρM `∙ V} {ρN `∙ W}
                                             (log-frm-apx₀^Ext apxρ sVW)
    ... | prf rewrite lemma34 (Q ⟪ M ⟫) ρM V | lemma34 (Q ⟪ N ⟫) ρN W = prf

lemma-4-15O : ∀ {Γ} {τ} {M N} → log-frm-apx M N →
  vsc-apx {`trm} {Γ} {τ} M N
lemma-4-15O {Γ} {τ} {M} {N} sMN P
  with lemma-4-14 P {M} {N} sMN ([ log-frm-apx₀^V ]^Env-refl₀ ι^Env)
... | prf = log-frm-apx-gnd-eqv₀ {`trm} sPMN
 where
  sPMN : log-frm-apx₀^T (P ⟪ M ⟫) (P ⟪ N ⟫)
  sPMN rewrite ι^Env₀-lemma (mkEnv (λ {σ} → `var)) (P ⟪ M ⟫) |
               ι^Env₀-lemma (mkEnv (λ {σ} → `var)) (P ⟪ N ⟫) = prf

log-frm-apx₀-lift : ∀ {σ} {V W} → log-frm-apx₀^V {σ} V W →
                    log-frm-apx₀ (`val V) (`val W)
log-frm-apx₀-lift {V = V} {W = W} sVW {τ} {S} {T} sST evSV = sST sVW evSV

Lemma-4-15 : (f : CBV) → Set
Lemma-4-15 f = ∀ {τ} {M N} → log-frm-apx₀ M N → vsc-apx₀ {f} {τ} M N
lemma-4-15 : ∀ {f} → Lemma-4-15 f
lemma-4-15 {f} = case f return Lemma-4-15 of
  λ { `val → prfV ; `trm → prfT }
 where
  prfV : Lemma-4-15 `val
  prfT : Lemma-4-15 `trm
  prfV {M = V} {N = W} = prfT ∘ log-frm-apx₀-lift
  prfT = lemma-4-15O ∘ (log-frm-apx₀-log-frm-apx {`trm})

Lemma-4-16 : (f : CBV) → Set
Lemma-4-16 f = ∀ {τ} {M N P} → app-frm-apx₀ M N → log-frm-apx₀ N P →
                   log-frm-apx₀ {f} {τ} M P
lemma-4-16 : ∀ {f} → Lemma-4-16 f
lemma-4-16 {f} = case f return Lemma-4-16 of
  λ { `val →  prfV ; `trm → prfT  }
 where
  prfV : Lemma-4-16 `val
  prfT : Lemma-4-16 `trm
  prfV {`b β} {`var ()}
  prfV {`b β} {`b b} (app-frm-apx₀^V-b _) r = r
  prfV {σ `→ τ} {`var ()}
  prfV {σ `→ τ} {`λ M} {P = `var ()}
  prfV {σ `→ τ} {`λ M} {P = `λ P} (app-frm-apx₀^V-λ sMN) r {U} {V} sUV =
    prfT (sMN U) (r sUV)

  prfT {τ} {M} {N} {P} sMN sNP {σ} {S} sST evSM with sMN evSM
  ... | V , evSN , sUV with sNP sST evSN
  ... | W , evTP , sVW = W , evTP , gnd-eqv₀-trans {`val} sUV sVW

lemma-4-17 : ∀ {f} {τ} {M N} → app-frm-apx₀ M N → log-frm-apx₀ {f} {τ} M N
lemma-4-17 {f} {τ} {M} {N} sMN =
  lemma-4-16 {f} {τ} sMN (log-frm-apx₀-refl N)

lemma-4-17O : ∀ {Γ} {τ} {M N : Trm τ Γ} →
  app-frm-apx M N → log-frm-apx M N
lemma-4-17O {Γ} {τ} {M} {N} sMN {ρM} {ρN} apxρ =
  lemma-4-16 {`trm} (sMN ρM) (log-frm-apx-refl N apxρ)
