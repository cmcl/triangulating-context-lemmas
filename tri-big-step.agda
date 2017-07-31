{-------------------------------------}
{- Triangle for Big-step evaluation. -}
{-------------------------------------}
module tri-big-step where

open import Level as L using (Level ; _⊔_)
open import Data.Bool renaming (true to tt ; false to ff)
open import Data.Product hiding (map)
open import Function as F hiding (_∋_ ; _$_)

open import Relation.Binary.PropositionalEquality as PEq using (_≡_)

open import lambda-fg
open import acmm
open import relations
open import big-step-prop
open import vcc-apx
open import obs-apx

{-------------------------------------}
{-- Big-step Approximation relations -}
{-------------------------------------}

{- a pattern
Lemma-XXX : (f : CBV) → Set
Lemma-XXX f = ?
lemma-XXX : ∀ {f} → Lemma-XXX f
lemma-XXX {f} = case f return Lemma-XXX of λ { `val →  prfV ; `trm → prfT  }
 where
  prfV : Lemma-XXX `val
  prfT : Lemma-XXX `trm
  prfV = ?
  prfT = ?
  lemma  : Lemma-XXX ?
  lemma  = ?
-}

-- Ground applicative contextual simulation

App-cxt-sim₀ : (f : CBV) → Set₁
App-cxt-sim₀ f = ∀ {τ} → GRel^E {f} {L.zero} {τ}
app-cxt-sim₀ : ∀ {f} → App-cxt-sim₀ f
app-cxt-sim₀ {f} = case f return App-cxt-sim₀ of
  λ { `val →  simV ; `trm → simT  }
 where
  simV : App-cxt-sim₀ `val
  simT : App-cxt-sim₀ `trm
  simV {τ}   = _[ simT {τ} ]^V_
  simT  {`b β}  M N = sim₀ M N
  simT {σ `→ τ} M N = sim₀ M N × (∀ U → simT {τ} (appT M U) (appT N U))

-- open extension of app-cxt-sim₀
App-cxt-sim : (f : CBV) → Set₁
App-cxt-sim f = ∀ {Γ} {τ} → Rel^E {f} {L.zero} {Γ} {τ}
app-cxt-sim : ∀ {f} → App-cxt-sim f
app-cxt-sim {f} = case f return App-cxt-sim of
  λ { `val →  simV ; `trm → simT  }
 where
  simV : App-cxt-sim `val
  simT : App-cxt-sim `trm
  simV {Γ} {τ} = _[ simT {Γ} {τ} ]^V_
  simT {Γ} {τ} = _[ app-cxt-sim₀ {`trm} {τ} ]^O_

-- Applicative simulation
mutual

 app-sim₀ : GRel₀^E
 app-sim₀ = λ { {`val} → app-sim₀^V ; {`trm} → app-sim₀^T }

 data
  app-sim₀^B : GRel₀^B where

   app-sim₀^B-b : ∀ {β} {b b'} → sim₀^B {β} b b' →
    app-sim₀^B {β} b b'

 data
  app-sim₀^V : GRel₀^V where

   app-sim₀^V-b : ∀ {β} {b b'} → app-sim₀^B {β} b b' →
    app-sim₀^V {`b β} (`b b) (`b b')

   app-sim₀^V-λ : ∀ {σ τ} {M N} →
      (∀ U → app-sim₀^T {τ} (M ⟨ U /var₀⟩) (N ⟨ U /var₀⟩)) →
               app-sim₀^V {σ `→ τ} (`λ M) (`λ N)

 app-sim₀^T : GRel₀^T
 app-sim₀^T {τ} M N = M [ app-sim₀^V {τ} ]^T N

-- open extension of app-sim₀
App-sim : ∀ (f : CBV) → Set₁
App-sim f = ∀ {Γ} {τ} → Rel^E {f} {L.zero} {Γ} {τ}
app-sim : ∀ {f} → App-sim f
app-sim {f} = case f return App-sim of λ { `val →  simV ; `trm → simT  }
 where
  simV : App-sim `val
  simT : App-sim `trm
  simV {Γ} {τ} = _[ simT {Γ} {τ} ]^V_
  simT {Γ} {τ} = _[ app-sim₀ {`trm} {τ} ]^O_

--
App-sim₀-refl : (f : CBV) → Set
App-sim₀-refl f = ∀ {τ} E → app-sim₀ {f} {τ} E E
app-sim₀-refl : ∀ {f} → App-sim₀-refl f
app-sim₀-refl {f} = case f return App-sim₀-refl of
  λ { `val →  prfV ; `trm → prfT }
 where
  prfV : App-sim₀-refl `val
  prfT : App-sim₀-refl `trm
  prfV  {`b β}  (`var ())
  prfV  {`b β}   (`b b)  = app-sim₀^V-b {b = b} (app-sim₀^B-b (sim₀^B-b b))

  prfV {σ `→ τ} (`var ())
  prfV {σ `→ τ}  (`λ M)  = app-sim₀^V-λ (λ U → prfT {τ} (M ⟨ U /var₀⟩))

  prfT {τ} = lemma-[ prfV {τ} ]^T-refl

app-sim₀^V-βV-λ : ∀ {σ τ} {M N} → (∀ U → app-sim₀^T (βV M U) (βV N U)) →
 app-sim₀^V {σ `→ τ} (`λ M) (`λ N)
app-sim₀^V-βV-λ r =
  app-sim₀^V-λ (λ U → lemma-2-10i →₁app (lemma-2-10ii (r U) →₁app))

app-sim₀^T-appT : ∀ {σ τ} {M N} →
 (∀ U → app-sim₀^T {τ} (appT M U) (appT N U)) →
 (sim₀^T M N) → app-sim₀^T {σ `→ τ} M N

app-sim₀^T-appT {σ} {τ} r = lemma-[-]^T-sim₀-λ {R = app-sim₀^V}
 (λ derM derN → app-sim₀^V-βV-λ (λ U → lemma-[-]^T-βV derM (r U) derN))

lemma-2-11B : ∀ {β} {V W : Val₀ (`b β)} →
  sim₀^V {`b β} V W → app-sim₀^V {`b β} V W
lemma-2-11B (sim₀^V-b (sim₀^B-b b)) = app-sim₀-refl (`b b)

Lemma-2-11 : (f : CBV) → Set
Lemma-2-11 f = ∀ {τ} {M N} → app-cxt-sim₀ M N → app-sim₀ {f} {τ} M N
lemma-2-11 : ∀ {f} → Lemma-2-11 f
lemma-2-11 {f} = case f return Lemma-2-11 of λ { `val →  prfV ; `trm → prfT  }
 where
  prfV : Lemma-2-11 `val
  prfT : Lemma-2-11 `trm
  prfV  {`b β} sVW = lemma-2-11B (T^V^[ sVW ]^V)

  prfV {σ `→ τ} {`var ()}
  prfV {σ `→ τ}  {`λ M} {`var ()}
  prfV {σ `→ τ}  {`λ M}  {`λ N} sMN = T^V^[ prfT sMN ]^V

  prfT  {`b β}          = lemma-[ lemma-2-11B {β} ]^T-mono
  prfT {σ `→ τ} (s , r) = app-sim₀^T-appT (λ U → prfT (r U)) s

lemma-2-11O : ∀ {Γ} {τ} {M N} →
  app-cxt-sim M N → app-sim {`trm} {Γ} {τ} M N
lemma-2-11O {Γ} {τ} sMN = lemma-2-11 {`trm} {τ} ∘ sMN

-- Logical simulation
log-sim₀ : GRel₀^E
log-sim₀^V : GRel₀^V
log-sim₀^T : GRel₀^T
{- *** Z-BEND *** -}
log-sim₀ {`val} = log-sim₀^V
log-sim₀ {`trm} = log-sim₀^T

log-sim₀^V {`b β} (`var ())
log-sim₀^V {`b β}  (`b b) (`var ())
log-sim₀^V {`b β}  (`b b)  (`b b') = sim₀^B b b'

log-sim₀^V {σ `→ τ} (`var ())
log-sim₀^V {σ `→ τ}  (`λ M) (`var ())
log-sim₀^V {σ `→ τ}  (`λ M)  (`λ N)  =
  ∀ {V W} → log-sim₀^V V W → log-sim₀^T (M ⟨ V /var₀⟩) (N ⟨ W /var₀⟩)

log-sim₀^T {τ} = _[ log-sim₀^V {τ} ]^T_

log-sim^B-refl : ∀ {β} b → log-sim₀^V {`b β} (`b b) (`b b)
log-sim^B-refl {β} b = sim₀^B-b b

-- a useful lemma, needed in 2.18O below
Log-sim-sim₀ : (f : CBV) → Set
Log-sim-sim₀ f = ∀ {σ} {M N} → log-sim₀ M N → sim₀ {f} {σ} M N
log-sim-sim₀ : ∀ {f} → Log-sim-sim₀ f
log-sim-sim₀ {f} = case f return Log-sim-sim₀ of
  λ { `val → prfV ; `trm → prfT }
 where
  prfV : Log-sim-sim₀ `val
  prfT : Log-sim-sim₀ `trm
  prfV {M = `var ()}
  prfV  {M = `b b} {N = `var ()}
  prfV  {M = `b b}  {N = `b b'} = sim₀^V-b

  prfV {M = `λ M} {`var ()}
  prfV {M = `λ M} {N = `λ N} _ = sim₀^V-λ

  prfT {σ} = lemma-[ prfV {σ} ]^T-mono

-- analogues of alternative introductions for app-sim at λs/higher type
log-sim₀-βV-λ : ∀ {σ τ} {M N} →
 (∀ {V W} → log-sim₀ V W → log-sim₀ (βV M V) (βV N W)) →
 log-sim₀^V {σ `→ τ} (`λ M) (`λ N)
log-sim₀-βV-λ r = λ U → lemma-2-10i →₁app (lemma-2-10ii (r U) →₁app)

log-sim₀-appT : ∀ {σ τ} {M N} →
 (∀ {V W} → log-sim₀ V W → log-sim₀ (appT M V) (appT N W)) →
 sim₀ M N → log-sim₀^T {σ `→ τ} M N
log-sim₀-appT {σ} {τ} r = lemma-[-]^T-sim₀-λ {R = log-sim₀^V}
 (λ derM derN → log-sim₀-βV-λ (λ U → lemma-[-]^T-βV derM (r U) derN))

-- now must develop fundamental lemma 2.16!
-- which might best be done by adapting Simulation from Allais et al.
-- take it slowly!

-- warm-up congruence rules: need expansion versions of lemma-2-10

log-sim₀^T-app : ∀ {σ τ} {f g} {a b} →
  log-sim₀^V {σ `→ τ} f g → log-sim₀ a b → log-sim₀ (f `$ a) (g `$ b)
log-sim₀^T-app = lemma-[-]^T-app {R = log-sim₀^V} (λ sVW sMN → sMN sVW)

log-sim₀^T-if : ∀ {σ} {b b'} {l l' r r'} → log-sim₀ b b' →
 log-sim₀ l l' → log-sim₀ r r' → log-sim₀^T {σ} (`if b l r) (`if b' l' r')
log-sim₀^T-if = lemma-[-]^T-if {R = log-sim₀^V} idB -- sim₀^B-refl-inv
 where
  idB : {b b' : ⟦ `B ⟧B} → log-sim₀ (`b b) (`b b') → b ≡ b'
  idB (sim₀^B-b b) = PEq.refl

log-sim₀^T-let : ∀ {σ τ} {M M'} {N N'} → (log-sim₀^T {σ} M M') →
 (∀ {V W} → log-sim₀ V W → log-sim₀ (N ⟨ V /var₀⟩) (N' ⟨ W /var₀⟩)) →
 log-sim₀^T {τ} (`let M N) (`let M' N')

log-sim₀^T-let = lemma-[-]^T-let {R = log-sim₀^V}

log-sim₀^Ext : ∀ {σ} {V W : Val₀ σ} {Γ} {ρ ρ' : Env₀ Γ}
               (simρ : ρ [ log-sim₀^V ]^Env ρ') (sVW : log-sim₀ V W) →
               (ρ `∙ V) [ log-sim₀^V ]^Env (ρ' `∙ W)
log-sim₀^Ext simρ sVW = _∙₀^R_ {𝓔^R = log-sim₀^V} simρ sVW

 -- fundamental definition on open terms

log-sim : ∀ {f} {Γ} {τ} → Rel^E {f} {_} {Γ} {τ}
log-sim = _O^[ log-sim₀ ]^O_

-- lifting closed to open

Log-sim₀-log-sim : (f : CBV) → Set
Log-sim₀-log-sim f = ∀ {σ} {M N} → log-sim₀ M N → log-sim {f} {ε} {σ} M N

log-sim₀-log-sim : ∀ {f} → Log-sim₀-log-sim f
log-sim₀-log-sim {f} = case f return Log-sim₀-log-sim of
  λ { `val → prfV ; `trm → prfT }
 where
  prfV : Log-sim₀-log-sim `val
  prfT : Log-sim₀-log-sim `trm
  prfV {σ} {V} {W} sVW simρ =
    T^V^[ prfT {σ} {`val V} { `val W} V^[ sVW ]^T^V simρ ]^V
  prfT {σ} {M} {N} sMN {ρM} {ρN} simρ = prf
   where
    prf : log-sim₀^T (subst M ρM) (subst N ρN)
    prf rewrite ι^Env₀-lemma ρM M | ι^Env₀-lemma ρN N = sMN

-- now we begin in earnest: fundamental lemma on open terms
-- here we go: not much to it! but it should be an instance of sim-lemma
lemma-2-16 : ∀ {f} {Γ} {τ} (E : Exp {f} τ Γ) → log-sim E E
lemma-2-16 (`var v) simρ = simρ v
lemma-2-16  (`b b)  simρ = log-sim^B-refl b

lemma-2-16  (`λ M) {ρ} {ρ'} simρ {V} {W} sVW
 with lemma-2-16 M (log-sim₀^Ext simρ sVW)
... | prf rewrite lemma34 M ρ V | lemma34 M ρ' W = prf

lemma-2-16   (`val V)       = V^[_]^T^V ∘ (lemma-2-16 V)
lemma-2-16   (f `$ a)  simρ = log-sim₀^T-app F A
 where F = lemma-2-16 f simρ ; A = lemma-2-16 a simρ
lemma-2-16 (`if b l r) simρ = log-sim₀^T-if B L R
 where B = lemma-2-16 b simρ ; L = lemma-2-16 l simρ ; R = lemma-2-16 r simρ
lemma-2-16 (`let M N) {ρ} {ρ'} simρ = log-sim₀^T-let prfM prfN
 where
  prfM = lemma-2-16 M simρ
  S = subst N (ext₀^Env ρ) ; S' = subst N (ext₀^Env ρ')

  prfN : ∀ {V W} → log-sim₀ V W → log-sim₀ (S ⟨ V /var₀⟩) (S' ⟨ W /var₀⟩)
  prfN {V} {W} sVW with lemma-2-16 N (log-sim₀^Ext simρ sVW)
  ... | prf rewrite lemma34 N ρ V | lemma34 N ρ' W = prf

-- Ground reflexivity is then a trivial corollary.
Log-sim₀-refl : (f : CBV) → Set
Log-sim₀-refl f = ∀ {τ} E → log-sim₀ {f} {τ} E E
log-sim₀-refl : ∀ {f} → Log-sim₀-refl f
log-sim₀-refl {f} = case f return Log-sim₀-refl of
  λ { `val →  prfV ; `trm → prfT }
 where
  prfV : Log-sim₀-refl `val
  prfT : Log-sim₀-refl `trm
  prfV {`b β} (`var ())
  prfV {`b β}  (`b b) = log-sim^B-refl {β} b

  prfV {σ `→ τ} (`var ())
  prfV {σ `→ τ}  (`λ M) sVW = lemma-2-16 M (Val₀→Env₀ {𝓔^R = log-sim₀^V} sVW)

  prfT {τ} = lemma-[ prfV {τ} ]^T-refl

-- Lemma 2.20 follows from the following generalisation of transitivity, plus
-- reflexivity.

Lemma-2-20-aux : (f : CBV) → Set
Lemma-2-20-aux f = ∀ {τ} {M N P} →
  app-sim₀ M N → log-sim₀ N P → log-sim₀ {f} {τ} M P
lemma-2-20-aux : ∀ {f} → Lemma-2-20-aux f
lemma-2-20-aux {f} = case f return Lemma-2-20-aux of
  λ { `val →  prfV ; `trm → prfT  }
 where
  prfV : Lemma-2-20-aux `val
  prfT : Lemma-2-20-aux `trm
  prfV  {`b β} {`var ()}
  prfV  {`b β}  {`b .b} (app-sim₀^V-b (app-sim₀^B-b (sim₀^B-b b))) r = r

  prfV {σ `→ τ} {`λ M} {`λ N} {`var ()} (app-sim₀^V-λ l) r
  prfV {σ `→ τ} {`λ M} {`λ N}  {`λ P}   (app-sim₀^V-λ l) r
   = λ {V} sMN → prfT (l V) (r sMN)

  prfT {τ} = lemma-[ prfV {τ} ]^T-trans

lemma-2-20 : ∀ {f} {τ} {M N} → app-sim₀ M N → log-sim₀ {f} {τ} M N
lemma-2-20 {f} {τ} {M} {N} sMN = lemma-2-20-aux {f} {τ} sMN (log-sim₀-refl N)

-- now use fundamental lemma 2.16, and generalised transitivity above,
-- to conclude on open terms
lemma-2-20O : ∀ {Γ} {τ} {M N : Trm τ Γ} → app-sim M N → log-sim M N
lemma-2-20O {Γ} {τ} {M} {N} sMN {ρM} {ρN} simρ =
  lemma-2-20-aux {`trm} (sMN ρM) (lemma-2-16 N simρ)

-- The reduction to applicative contexts.
-- Lemma 2.6, done as smoothly as possible.

-- second version: this is really a lemma about *open* terms

-- lifting up to applicative contexts requires a little more work
lemma-2-6O : ∀ {Γ} {τ} {M N} → cxt-sim M N → app-cxt-sim {`trm} {Γ} {τ} M N
lemma-2-6O {Γ}  {`b β}                = cxt-sim→sim^T
lemma-2-6O {Γ} {σ `→ τ} {M} {N} sMN ρ = cxt-sim→sim^T sMN ρ , lemma2-6-appT₀
 where
  -- basic applicative setting, relative to the valuation ρ
  appT₀ : (M : Exp (σ `→ τ) Γ) (U : Val₀ σ) → Trm₀ τ
  appT₀ M U = appT (subst M ρ) U

  -- appT₀ reified as a one-hole context
  appP₀ : (U : Val₀ σ) → Cxt⟪ Γ ⊢ σ `→ τ ⟫ τ ε
  appP₀ U = `let ⟪- ρ -⟫ (`exp (Val→Spine U))

  -- hence cxt-sim₀ is closed under appT₀, modulo rewrites
  sim-appT₀ : ∀ U → cxt-sim₀ (appT₀ M U) (appT₀ N U)
  sim-appT₀ U P with sMN (P ⟪∘⟫ appP₀ U)
  ... | prf rewrite P ⟪∘ M ⟫ appP₀ U | P ⟪∘ N ⟫ appP₀ U = prf

  -- and hence likewise, finally, app-cxt-sim₀ itself,
  -- by IH at type τ (via dummy valuation ι^Env, more rewrites)
  lemma2-6-appT₀ : ∀ U → app-cxt-sim₀ (appT₀ M U) (appT₀ N U)
  lemma2-6-appT₀ U with lemma-2-6O {Γ = ε} {τ = τ} (sim-appT₀ U) ι^Env
  ... | prf rewrite ι^Env₀ (appT₀ M U) | ι^Env₀ (appT₀ N U) = prf

lemma-2-6 : ∀ {τ} {M N} → cxt-sim₀ M N → app-cxt-sim₀ {`trm} {τ} M N
lemma-2-6 {τ} {M} {N} sMN with lemma-2-6O sMN ι^Env
... | prf rewrite ι^Env₀ M | ι^Env₀ N = prf

infixl 9 _<:_

_<:_ : Cx → Ty → Cx
ε <: σ = ε ∙ σ
Γ ∙ τ <: σ = (Γ <: σ) ∙ τ

-- appT₀ (see below) reified as a one-hole VCC context: substitution occurs at
-- top-level.
app⟪-⟫ : ∀ {Γ} {σ τ} → (U : Val σ Γ) → VCC⟪ Γ ⊢ σ `→ τ ⟫ τ Γ
app⟪-⟫ U = `let ⟪- refl^Var -⟫ (`exp (Val→Spine U))

-- subst-inst-commute : ∀ {Γ} {σ τ ω} → (P : VCC⟪ ε ⊢ σ ⟫ {`trm} τ ε) →
--   (U : Val₀ ω) → (M : Trm (ω `→ σ) Γ) → (ρ : Γ ⊨ ε) →
--   subst (barC' {ε} P Γ ⟪ app⟪-⟫ (Ren₀ *-Var U) ⟪ M ⟫VCC ⟫VCC) ρ ≡
--     P ⟪ app⟪-⟫ U ⟪ subst M ρ ⟫VCC ⟫VCC
-- subst-inst-commute = {!!}

ι^Env-ext-lemma : ∀ {f} {Γ} {ω σ τ} → (E : Exp {f} ω (Γ ∙ σ ∙ τ)) →
  (ext₀^Env (ext₀^Env ι^Env) *-Val E) ≡ E
ι^Env-ext-lemma = ι^Env-lemma-aux {ρ = ext₀^Env (ext₀^Env ι^Env)}
  (ext₀^Env-ext₀ {ρ = ext₀^Env ι^Env} (ext₀^Env-ext₀ {ρ = ι^Env}
    (λ v → PEq.refl)))

ext₀^Var-ext : ∀ {Γ Δ} {σ} → {r r' : Γ ⊆ Δ} →
                 (∀ {τ} v → var r {τ} v ≡ var r' v) →
 ∀ {τ} v → var (ext₀^Var {σ} {Γ} r) {τ} v ≡ var (ext₀^Var r') v
ext₀^Var-ext {Γ} {Δ} {σ} {r} {r'} eq =
  [ P ][ PEq.refl ,,,  PEq.cong su ∘ eq ]
 where P = λ {τ} v → var (ext₀^Var {σ} {Γ} r) {τ} v ≡ var (ext₀^Var r') v

ren-ext : ∀ {f} {Γ Δ} {σ} → (E : Exp {f} σ Γ) →
 {r r' : Γ ⊆ Δ} → (∀ {τ} v → var r {τ} v ≡ var r' v) →
 ren E r ≡ ren E r'
ren-ext (`var v) prf = PEq.cong `var (prf v)
ren-ext (`b b) prf = PEq.refl
ren-ext (`λ M) prf rewrite ren-ext M (ext₀^Var-ext prf) = PEq.refl
ren-ext (`val M) prf rewrite ren-ext M prf = PEq.refl
ren-ext (F `$ A) prf rewrite ren-ext F prf | ren-ext A prf = PEq.refl
ren-ext (`if B L R) prf
  rewrite ren-ext B prf | ren-ext L prf | ren-ext R prf = PEq.refl
ren-ext (`let M N) prf
  rewrite ren-ext M prf | ren-ext N (ext₀^Var-ext prf) = PEq.refl

-- The same proof as for ext₀^Env-ext₀ but I cannot think how to generalise
-- the statement to encompass both.
ext₀^Env^Var-ext₀ : ∀ {Γ Δ} {σ} → {r : Γ ⊆ Δ} → {ρ : Δ ⊨ Γ} →
  (∀ {τ} v → var ρ {τ} (var r v) ≡ `var v) →
 ∀ {τ} v → var (ext₀^Env {σ} {Δ} ρ) {τ} (var (ext₀^Var r) v) ≡ `var v
ext₀^Env^Var-ext₀ {Γ} {Δ} {σ} {r} {ρ} eq =
  [ P ][ PEq.refl ,,, (PEq.cong (weak *-Var_)) ∘ eq ]
  where
    P = λ {τ} v → var (ext₀^Env {σ} {Δ} ρ) {τ} (var (ext₀^Var r) v) ≡ `var v

ren-sub : ∀ {f} {Γ Δ} {σ} →
  (E : Exp {f} σ Γ) → (r : Γ ⊆ Δ) → (ρ : Δ ⊨ Γ) →
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

weak-sub : ∀ {f} {Γ} {σ τ} → (V : Val τ Γ) → (E : Exp {f} σ Γ) →
  (weak *-Var E) ⟨ V /var₀⟩ ≡ E
weak-sub V E = ren-sub E weak (ι^Env `∙ V) (λ v → PEq.refl)

weak-ext₀^Var-comm : ∀ {Γ Δ} {σ} {r : Γ ⊆ Δ} →
 ∀ {τ} v → var weak {τ} (var r v) ≡ var (ext₀^Var {σ} r) (var weak v)
weak-ext₀^Var-comm v = PEq.refl

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

swp : ∀ {Γ} {σ τ} → Γ ∙ σ ∙ τ ⊆ Γ ∙ τ ∙ σ
var swp ze = su ze
var swp (su ze) = ze
var swp (su (su v)) = su (su v)

barC : ∀ {f} {Γ Δ} {σ τ ω} → VCC⟪ Γ ⊢ ω ⟫ {f} τ Δ →
  VCC⟪ Γ ∙ σ ⊢ ω ⟫ {f} τ (Δ ∙ σ)
barC {σ = σ} (`λ {ν} M) = `λ (renC (barC M) swp)
barC (`exp E) = `exp (weak *-Var E)
barC ⟪- r -⟫ = ⟪- pop! r -⟫
barC (`val C) = `val (barC C)
barC (F `$ A) = (barC F) `$ (barC A)
barC (`if B L R) = `if (barC B) (barC L) (barC R)
barC {σ = σ} (`let {ν} M N) = `let (barC M) (renC (barC N) swp)

renC-VCC : ∀ {f} {Γ Δ Ξ} {σ ω} → (P : VCC⟪ Ξ ⊢ σ ⟫ {f} ω Γ) → (M : Trm σ Ξ) →
 {r r' : Γ ⊆ Δ} → (∀ {τ} v → var r {τ} v ≡ var r' v) →
 renC P r ⟪ M ⟫VCC ≡ renC P r' ⟪ M ⟫VCC
renC-VCC (`λ P) M eq rewrite renC-VCC P M (ext₀^Var-ext eq) = PEq.refl
renC-VCC (`exp E) M eq = ren-ext E eq
renC-VCC ⟪- ρ -⟫ M {r} {r'} eq
  rewrite lemma33-ren r ρ M | lemma33-ren r' ρ M = ren-ext (ren M ρ) eq
renC-VCC (`val P) M eq rewrite renC-VCC P M eq = PEq.refl
renC-VCC (F `$ A) M eq rewrite renC-VCC F M eq | renC-VCC A M eq = PEq.refl
renC-VCC (`if B L R) M eq
  rewrite renC-VCC B M eq | renC-VCC L M eq | renC-VCC R M eq = PEq.refl
renC-VCC (`let P Q) M eq rewrite renC-VCC P M eq |
                                 renC-VCC Q M (ext₀^Var-ext eq) = PEq.refl

ren-ren : ∀ {f} {Γ Δ Ξ Ω} {σ τ} →
  (P : VCC⟪ Γ ⊢ σ ⟫ {f} τ Δ) → (M : Trm σ Γ) → (r : Δ ⊆ Ξ) → (r' : Ξ ⊆ Ω) →
  renC (renC P r) r' ⟪ M ⟫VCC ≡ renC P (trans^Var r r') ⟪ M ⟫VCC
ren-ren (`λ P) M r r' with renC-VCC P M (pop!-trans {inc₁ = r} {inc₂ = r'})
... | ren-eq rewrite ren-eq |
                     ren-ren P M (ext₀^Var r) (ext₀^Var r') = PEq.refl
ren-ren (`exp E) M r r' = PEq.sym (lemma33-ren r' r E)
ren-ren ⟪- ρ -⟫ M r r' rewrite lemma33-ren (trans^Var r r') ρ M |
                               lemma33-ren r' (trans^Var ρ r) M |
                               lemma33-ren r' r (ren M ρ) |
                               lemma33-ren r ρ M = PEq.refl
ren-ren (`val P) M r r' rewrite ren-ren P M r r' = PEq.refl
ren-ren (F `$ A) M r r' rewrite ren-ren F M r r' | ren-ren A M r r' = PEq.refl
ren-ren (`if B L R) M r r'
  rewrite ren-ren B M r r' | ren-ren L M r r' | ren-ren R M r r' = PEq.refl
ren-ren (`let P Q) M r r' rewrite ren-ren P M r r'
  with renC-VCC Q M (pop!-trans {inc₁ = r} {inc₂ = r'})
... | ren-eq rewrite ren-eq |
                     ren-ren Q M (ext₀^Var r) (ext₀^Var r') = PEq.refl

infixl 7 _,,_

_,,_ : Cx → Cx → Cx
Γ ,, ε = Γ
Γ ,, (Δ ∙ τ) = (Γ ,, Δ) ∙ τ

push : ∀ {Γ Δ} → (Ξ : Cx) → Γ ⊨ Δ → Γ ,, Ξ ⊨ Δ ,, Ξ
push ε ρ = ρ
push (Ξ ∙ τ) ρ = ext₀^Env (push Ξ ρ)

ren-perm-ext : ∀ {Δ Ξ} {σ τ} → (Δ ,, Ξ) ∙ σ ⊆ (Δ ∙ σ) ,, Ξ →
  (Δ ,, Ξ) ∙ τ ∙ σ ⊆ (Δ ∙ σ) ,, Ξ ∙ τ
ren-perm-ext r = swp *-Env (ext₀^Var r)

swp-ext₀^Env : ∀ {Γ} {σ ω} → (V : Val₀ σ) →
  ∀ {τ} v → var (ext₀^Env {ω} (ι^Env {Γ} `∙ ren V Ren₀)) {τ}
                              (var (weak *-Env swp) v) ≡ `var v
swp-ext₀^Env V ze = PEq.refl
swp-ext₀^Env V (su v) = PEq.refl

push-ren-perm :  ∀ {Γ Δ} {σ ω} →
  (V : Val₀ σ) → (r : (Γ ,, Δ) ∙ σ ⊆ Γ ∙ σ ,, Δ) →
  (prf : ∀ {τ} v → var (push Δ (ι^Env `∙ ren V Ren₀)) {τ}
                         (var (weak *-Env r) v) ≡ `var v) →
  ∀ {τ} v → var (push (Δ ∙ ω) (ι^Env `∙ ren V Ren₀)) {τ}
           (var (weak *-Env ren-perm-ext {Γ} {Δ} {σ} {ω} r) v) ≡ `var v
push-ren-perm {Γ} {Δ} {σ} {ω} V r prf =
  [ P ][ PEq.refl ,,, PEq.cong (weak *-Var_) ∘ prf ]
  where P = λ {τ} v → var (push (Δ ∙ ω) (ι^Env `∙ ren V Ren₀)) {τ}
           (var (weak *-Env (ren-perm-ext {Γ} {Δ} {σ} {ω} r)) v) ≡ `var v

{-
push-pop!-comm : ∀ {Γ Δ Ξ} {σ} →
  (r : Γ ⊆ Δ ,, Ξ) → (r' : (Δ ,, Ξ) ∙ σ ⊆ Δ ∙ σ ,, Ξ) → (V : Val₀ σ) →
  ∀ {τ} v → var (push Ξ (ι^Env `∙ ren V Ren₀)) {τ} (var (pop! r *-Env r') v) ≡
                ren (var (ι^Env `∙ ren V Ren₀) v) r
push-pop!-comm r r' V ze rewrite weak-sub V V = {!!}
push-pop!-comm r r' V (su v) = {!!}
-}

-- ((ρ : Ω ⊆ (Δ ,, Ξ) ∙ σ) →
-- ∀ {τ} v → var (push Ξ (ι^Env `∙ ren V Ren₀)) (var (ρ *-Env r) v)
--       ≡ ren (var (ι^Env `∙

ren-bar : ∀ {f} {Γ Δ Ξ} {σ τ ω} →
  (P : VCC⟪ Γ ⊢ σ ⟫ {f} τ (Δ ,, Ξ)) → (V : Val₀ ω) →
  (M : Trm σ (Γ ∙ ω)) →
  (r : (Δ ,, Ξ) ∙ ω ⊆ Δ ∙ ω ,, Ξ) →
  (prf : ∀ {τ} v → var (push Ξ (ι^Env `∙ ren V Ren₀)) {τ}
                              (var (trans^Var weak r) v) ≡ `var v) →
  subst ((renC (barC P) r) ⟪ M ⟫VCC) (push Ξ (ι^Env `∙ ren V Ren₀)) ≡
    P ⟪ M ⟨ ren V Ren₀ /var₀⟩ ⟫VCC
ren-bar {`val} {Γ} {Δ} {Ξ} {ω = ω} (`λ {ν} P) V M r prf
  with ren-bar {Ξ = Ξ ∙ ν} P V M (ren-perm-ext {Δ} {Ξ} {ω} {ν} r)
               (push-ren-perm {Δ = Ξ} {ω = ν} V r prf)
... | ih rewrite ren-ren (barC P) M swp (ext₀^Var r) | ih = PEq.refl
ren-bar {Ξ = Ξ} (`exp E) V M r prf rewrite PEq.sym (lemma33-ren r weak E) =
  ren-sub E (weak *-Env r) (push Ξ (ι^Env `∙ ren V Ren₀)) prf
ren-bar ⟪- ρ -⟫ V M r prf = {!!}
ren-bar {Ξ = Ξ} (`val P) V M r prf
  rewrite ren-bar {Ξ = Ξ} P V M r prf = PEq.refl
ren-bar {Ξ = Ξ} (F `$ A) V M r prf
  rewrite ren-bar {Ξ = Ξ} F V M r prf | ren-bar {Ξ = Ξ} A V M r prf = PEq.refl
ren-bar {Ξ = Ξ} (`if B L R) V M r prf
  rewrite ren-bar {Ξ = Ξ} B V M r prf | ren-bar {Ξ = Ξ} L V M r prf |
          ren-bar {Ξ = Ξ} R V M r prf = PEq.refl
ren-bar {`trm} {Γ} {Δ} {Ξ} {ω = ω} (`let {ν} P Q) V M r prf
  rewrite ren-bar {Ξ = Ξ} P V M r prf
  with ren-bar {Ξ = Ξ ∙ ν} Q V M (ren-perm-ext {Δ} {Ξ} {ω} {ν} r)
               (push-ren-perm {Δ = Ξ} {ω = ν} V r prf)
... | ih rewrite ren-ren (barC Q) M swp (ext₀^Var r) | ih = PEq.refl

Ren₀-absorb : ∀ {Γ Δ} {r : Γ ⊆ Δ} →
  ∀ {τ} v → var Ren₀ {τ} v ≡ var (trans^Var Ren₀ r) v
Ren₀-absorb ()

ι^Env-pop!-comm : ∀ {Γ Δ} {σ} → (r : Γ ⊆ Δ) → (V : Val₀ σ) →
  ∀ {τ} v → var (ι^Env `∙ (Ren₀ *-Var V)) {τ} (var (pop! r) v) ≡
                (r *-Var (var (ι^Env `∙ (Ren₀ *-Var V)) v))
ι^Env-pop!-comm {Γ} {Δ} r V ze rewrite PEq.sym (lemma33-ren r Ren₀ V) =
  ren-ext V (Ren₀-absorb {r = r})
ι^Env-pop!-comm r V (su v) = PEq.refl

subst-inst-comm : ∀ {f} {Γ Δ Ξ} {σ τ ω} →
  (P : VCC⟪ Γ ⊢ σ ⟫ {f} τ Δ) → (V : Val₀ ω) → (M : Trm σ (Γ ∙ ω)) →
  (r1 : Ξ ⊆ Δ) → (r2 : Ξ ⊆ Γ) →
  (barC P) ⟪ M ⟫VCC ⟨ Ren₀ *-Var V /var₀⟩ ≡ P ⟪ M ⟨ Ren₀ *-Var V /var₀⟩ ⟫VCC
subst-inst-comm {ω = ω} (`λ {ν} P) V M r1 r2
  rewrite ren-bar {Ξ = ε ∙ ν} P V M swp (swp-ext₀^Env V) = PEq.refl
subst-inst-comm (`exp E) V M r1 r2 = weak-sub (Ren₀ *-Var V) E --
subst-inst-comm {`trm} {Γ} {Δ} ⟪- r -⟫ V M r1 r2 =
  ren-sub-prop M (pop! r) r (ι^Env `∙ (Ren₀ *-Var V))
                 (ι^Env `∙ (Ren₀ *-Var V)) (ι^Env-pop!-comm r V)
subst-inst-comm (`val P) V M r1 r2
  rewrite subst-inst-comm P V M r1 r2 = PEq.refl
subst-inst-comm (F `$ A) V M r1 r2
  rewrite subst-inst-comm F V M r1 r2 |
          subst-inst-comm A V M r1 r2 = PEq.refl
subst-inst-comm (`if B L R) V M r1 r2
  rewrite subst-inst-comm B V M r1 r2 | subst-inst-comm L V M r1 r2 |
          subst-inst-comm R V M r1 r2 = PEq.refl
subst-inst-comm (`let {ν} P Q) V M r1 r2
  rewrite subst-inst-comm P V M r1 r2 |
          ren-bar {Ξ = ε ∙ ν} Q V M swp (swp-ext₀^Env V) = PEq.refl

-- Γ-extended version of the above
_#_ : Cx → Cx → Cx
--ε # Δ = Δ
Γ # ε = Γ
Γ # (Δ ∙ τ) = (Γ ∙ τ) # Δ

emp-,, : (Γ : Cx) → ε ,, Γ ≡ Γ
emp-,, ε = PEq.refl
emp-,, (Γ ∙ τ) rewrite emp-,, Γ = PEq.refl

push-bwd : ∀ {Γ} → (Δ : Cx) → Γ ⊨ ε → Δ ,, Γ ⊨ Δ
push-bwd {ε} Δ ρ = ι^Env
push-bwd {Γ ∙ τ} Δ ρ = push-bwd Δ (suc ρ) `∙ (Ren₀ *-Var var ρ ze)

barCx : ∀ {f} {Γ Δ} {τ ω} → (Ξ : Cx) → VCC⟪ Γ ⊢ ω ⟫ {f} τ Δ →
  VCC⟪ Γ ,, Ξ ⊢ ω ⟫ {f} τ (Δ ,, Ξ)
barCx ε C = C
barCx (Ξ ∙ τ) C = barC {σ = τ} (barCx Ξ C)

barCx' : ∀ {f} {τ ω} → (Ξ : Cx) → VCC⟪ ε ⊢ ω ⟫ {f} τ ε →
  VCC⟪ Ξ ⊢ ω ⟫ {f} τ Ξ
barCx' ε C = C
barCx' (Ξ ∙ τ) C = barC {σ = τ} (barCx' Ξ C) --  (barCx Ξ C)

subst⟪-⟫ : ∀ {f} {Ξ} {σ τ}
  (P : VCC⟪ ε ⊢ σ ⟫ {f} τ ε) → (M : Trm σ Ξ) (ρ : Env₀ Ξ) →
  subst ((barCx' Ξ P) ⟪ M ⟫VCC) ρ ≡
    P ⟪ subst M ρ ⟫VCC
subst⟪-⟫ {Ξ = ε} P M ρ
  rewrite ι^Env₀-lemma ρ (P ⟪ M ⟫VCC) | ι^Env₀-lemma ρ M = PEq.refl
subst⟪-⟫ {f} {Ξ ∙ τ} P M ρ
  rewrite PEq.sym (subst-equiv ρ (barC (barCx' Ξ P) ⟪ M ⟫VCC)) |
          subst-equiv (suc ρ)
                      (barC (barCx' Ξ P) ⟪ M ⟫VCC ⟨ Ren₀ *-Var zero ρ /var₀⟩) |
          subst-inst-comm (barCx' Ξ P) (var ρ ze) M Ren₀ Ren₀
  with subst⟪-⟫ {Ξ = Ξ} P (M ⟨ Ren₀ *-Var (var ρ ze) /var₀⟩) (suc ρ)
... | ih rewrite PEq.sym (subst-equiv ρ M) |
                 subst-equiv (suc ρ) (M ⟨ Ren₀ *-Var zero ρ /var₀⟩) = ih

appT₀ : ∀ {Γ} {σ τ} → (ρ : Γ ⊨ ε) (M : Exp (σ `→ τ) Γ) (U : Val₀ σ) → Trm₀ τ
appT₀ ρ M U = appT (subst M ρ) U

appP : ∀ {Γ} {σ τ} → (U : Val₀ σ) → VCC⟪ Γ ⊢ σ `→ τ ⟫ τ Γ
appP U = `let ⟪- refl^Var -⟫ (`exp (Val→Spine (Ren₀ *-Var U)))

redVCC : ∀ {f} {Γ} {σ τ ν} → VCC⟪ ε ,, Γ ⊢ σ `→ τ ⟫ {f} ν (ε ,, Γ) →
  VCC⟪ Γ ⊢ σ `→ τ ⟫ {f} ν Γ
redVCC {f} {Γ} P with ε ,, Γ | emp-,, Γ
redVCC P | Γ | PEq.refl = P

-- ren-comm : ∀ {f} {Γ Δ Ω Ξ} {σ}
--   {r : Γ ⊆ Δ} {r' : Ω ⊆ Ξ} {ρ : Δ ⊆ Ξ} {ρ' : Γ ⊆ Ω} →
--   (E : Exp {f} σ Γ) → (∀ {τ} v → var ρ {τ} (var r v) ≡ var r' (var ρ' v)) →
--  (ρ *-Var (r *-Var E)) ≡ (r' *-Var (ρ' *-Var E))


ext₀^Env-weak : ∀ {Γ Δ} {σ} (ρ : Γ ⊨ Δ) →
  ∀ {τ} v → var (ext₀^Env {σ} ρ) {τ} (var weak v) ≡ (weak *-Var (var ρ v))
ext₀^Env-weak ρ v = PEq.refl

sim-appT₀ : ∀ {Γ} {σ τ} {M N : Exp (σ `→ τ) Γ} → (ρ : Γ ⊨ ε) → vcc-sim M N →
  (U : Val₀ σ) → vcc-sim₀ (appT₀ ρ M U) (appT₀ ρ N U)
sim-appT₀ {Γ} {σ} {τ} {M} {N} ρ sMN U {ν} P
  with sMN (VCC-sub ((barCx' Γ P) ⟪∘⟫VCC appP U) ρ)
... | prf with (λ M → VCC-betaV ρ M ((barCx' Γ P) ⟪∘⟫VCC (appP U)))
... | βV-VCC rewrite βV-VCC M | βV-VCC N
  with (λ M → (barCx' Γ P) ⟪∘ M ⟫VCC appP U)
... | ∘-⟪-⟫-comm rewrite ∘-⟪-⟫-comm M | ∘-⟪-⟫-comm N
  with (λ M → betaV-Trm ρ (barCx' Γ P ⟪ appP U ⟪ M ⟫VCC ⟫VCC))
... | βV→subst with lemma-2-10i-βV (βV→subst M)
                                   (lemma-2-10ii-βV prf (βV→subst N))
... | subst-sim rewrite subst⟪-⟫ P (appP U ⟪ M ⟫VCC) ρ |
                        subst⟪-⟫ P (appP U ⟪ N ⟫VCC) ρ |
                        ι^Var-lemma M | ι^Var-lemma N
  with ren-sub-prop (Ren₀ *-Var U)
                    (weak {σ = σ `→ τ}) weak (ext₀^Env ρ) ρ (ext₀^Env-weak ρ)
... | ren-sub-comm rewrite ren-sub-comm with ren-sub U Ren₀ ρ (λ())
... | sub-Ren₀ rewrite sub-Ren₀ = subst-sim

lemma-2-6O-VCC : ∀ {Γ} {τ} {M N} → vcc-sim M N →
  app-cxt-sim {`trm} {Γ} {τ} M N
lemma-2-6O-VCC {Γ} {`b β} = vcc-sim→sim^T
lemma-2-6O-VCC {Γ} {σ `→ τ} {M} {N} sMN ρ =
  (vcc-sim→sim^T sMN ρ) , lemma2-6-appT₀
 where
  -- basic applicative setting, relative to the valuation ρ
--  appT₀ : (M : Exp (σ `→ τ) Γ) (U : Val₀ σ) → Trm₀ τ
--  appT₀ M U = appT (subst M ρ) U

--  sim-appT₀ : ∀ U → vcc-sim₀ (appT₀ M U) (appT₀ N U)
--  sim-appT₀ U P with sMN (VCC-sub (redVCC ((barCx Γ P) ⟪∘⟫VCC appP (Ren₀ *-Var U))) ρ) | ε ,, Γ | emp-,, Γ
--  sim-appT₀ U P | hyp | Δ | prf = {!sMN!}

--  sim-appT₀ U P | pP | prf rewrite prf with sMN (VCC-sub pP ρ)
--with sMN (P ⟪∘⟫ appP₀ U)
--  ... | prf rewrite P ⟪∘ M ⟫ appP₀ U | P ⟪∘ N ⟫ appP₀ U = prf

  lemma2-6-appT₀ : ∀ U → app-cxt-sim₀ (appT₀ ρ M U) (appT₀ ρ N U)
  lemma2-6-appT₀ U
    with lemma-2-6O-VCC {Γ = ε} {τ = τ} (sim-appT₀ ρ sMN U) ι^Env
  ... | prf rewrite ι^Env₀ (appT₀ ρ M U) | ι^Env₀ (appT₀ ρ N U) = prf

{-

  appP : ∀ {Γ} {σ τ} → (U : Val σ Γ) → VCC⟪ Γ ⊢ σ `→ τ ⟫ τ Γ
  appP U = `let ⟪- refl^Var -⟫ (`exp (Val→Spine U))

  app-βV : (U : Val σ Γ) → (M : Trm (σ `→ τ) Γ) →
    (VCC-sub (appP U) ρ ⟪ M ⟫VCC) →βV subst ((appP U) ⟪ M ⟫VCC) ρ
  app-βV U M rewrite VCC-betaV ρ M (appP U) = {!!}

  VCC-make : ∀ {Γ} {σ τ} → Γ ⊨ ε → VCC⟪ Γ ⊢ σ ⟫ τ ε
  VCC-make {Γ} ρ = {!!}

  -- hence ivcc-sim₀ is closed under appT₀, modulo rewrites
  sim-appT₀ : ∀ U → vcc-sim₀ (appT₀ M U) (appT₀ N U)
  sim-appT₀ U P = {!!}
-}
{-
    with sMN (VCC-sub ρ ((barC {ε} P Γ) ⟪∘⟫VCC (appP (Ren₀ *-Var U))))
  ... | prf with VCC-sub-βV ρ ((barC {ε} P Γ) ⟪∘⟫VCC (appP (Ren₀ *-Var U)))
  ... | betaV rewrite betaV-Trm M | betaV-Trm N
          with (λ M → (barC {ε} P Γ) ⟪∘ M ⟫VCC appP (Ren₀ *-Var U))
  ... | comp-inst rewrite comp-inst M | comp-inst N with
    (λ M → βV-subst₀ ρ (barC {ε} P Γ ⟪ appP (Ren₀ *-Var U) ⟪ M ⟫IVCC ⟫IVCC))
  ... | sub-red with lemma-2-10i-βV (sub-red M)
                                   (lemma-2-10ii-βV prf (sub-red N))
  ... | red-sim with
    (λ M → subst-equiv ρ (barC {ε} P Γ ⟪ appP (Ren₀ *-Var U) ⟪ M ⟫IVCC ⟫IVCC))
  ... | sub-eq rewrite sub-eq M | sub-eq N |
                       subst-inst-commute P U M ρ |
                       subst-inst-commute P U N ρ = red-sim
-}
-- Now, Lemma 2.18, done using Ian's argument.

lemma-2-18-aux : ∀ {f} {Γ Δ} {τ υ} (P : Cxt⟪ Γ ⊢ τ ⟫ {f} υ Δ) →
 ∀ {M N} → log-sim M N → log-sim (P ⟪ M ⟫) (P ⟪ N ⟫)

lemma-2-18-aux (`exp E)          _           simρ = lemma-2-16 E simρ

lemma-2-18-aux  (`λ P) {M} {N} sMN {ρM} {ρN} simρ {V} {W} sVW
 with lemma-2-18-aux P {M} {N} sMN {ρM `∙ V} {ρN `∙ W} (log-sim₀^Ext simρ sVW)
... | prf rewrite lemma34 (P ⟪ M ⟫) ρM V | lemma34 (P ⟪ N ⟫) ρN W = prf

lemma-2-18-aux   ⟪- ρ -⟫   {M} {N} sMN {ρM} {ρN} simρ
 with sMN {ρM *-Sub ρ} {ρN *-Sub ρ} (λ {σ} v → lemma-2-16 (var ρ {σ} v) simρ)
... | prf rewrite lemma33 ρM ρ M | lemma33 ρN ρ N = prf

lemma-2-18-aux   (`val P)  {M} {N} sMN {ρM} {ρN} simρ
 with lemma-2-18-aux P {M} {N} sMN {ρM} {ρN} simρ
... | prf = V^[ prf ]^T^V

-- now it's just congruence rules (that's Ian's point)
lemma-2-18-aux   (F `$ A)  {M} {N} sMN {ρM} {ρN} simρ
 = log-sim₀^T-app (lemma-2-18-aux F sMN simρ) (lemma-2-18-aux A sMN simρ)

lemma-2-18-aux (`if B L R) {M} {N} sMN {ρM} {ρN} simρ
 = log-sim₀^T-if (lemma-2-18-aux B sMN simρ)
  (lemma-2-18-aux L sMN simρ) (lemma-2-18-aux R sMN simρ)

lemma-2-18-aux  (`let P Q) {M} {N} sMN {ρM} {ρN} simρ
 = log-sim₀^T-let (lemma-2-18-aux P sMN simρ) prfQ
  where
   QM = subst (Q ⟪ M ⟫) (ext₀^Env ρM) ; QN = subst (Q ⟪ N ⟫) (ext₀^Env ρN)
   prfQ : ∀ {V W} → log-sim₀ V W → log-sim₀ (QM ⟨ V /var₀⟩) (QN ⟨ W /var₀⟩)
   prfQ {V} {W} sVW
    with lemma-2-18-aux Q {M} {N} sMN {ρM `∙ V} {ρN `∙ W}
                        (log-sim₀^Ext simρ sVW)
   ... | prf rewrite lemma34 (Q ⟪ M ⟫) ρM V | lemma34 (Q ⟪ N ⟫) ρN W = prf

-- NEW reflecting Craig's new (sic) numbering; refactored the proof, too (sic)
lemma-2-19-aux : ∀ {Γ} {τ} {M N} → log-sim M N →
 ∀ {f} {Δ} {υ} (P : Cxt⟪ Γ ⊢ τ ⟫ {f} υ Δ) → log-sim (P ⟪ M ⟫) (P ⟪ N ⟫)

lemma-2-19-aux {Γ} {τ} {M} {N} sMN = lemma
 where
  lemma : ∀ {f} {Δ} {υ}
          (P : Cxt⟪ Γ ⊢ τ ⟫ {f} υ Δ) → log-sim (P ⟪ M ⟫) (P ⟪ N ⟫)

  lemma  (`exp E)   {ρM} {ρN} simρ = lemma-2-16 E simρ
  lemma   (`λ P)    {ρM} {ρN} simρ {V} {W} sVW
   with lemma P {ρM `∙ V} {ρN `∙ W} (log-sim₀^Ext simρ sVW)
  ... | prf rewrite lemma34 (P ⟪ M ⟫) ρM V | lemma34 (P ⟪ N ⟫) ρN W = prf
  lemma  ⟪- ρ -⟫    {ρM} {ρN} simρ
   with sMN {ρM *-Sub ρ} {ρN *-Sub ρ}
            (λ {σ} v → lemma-2-16 (var ρ {σ} v) simρ)
  ... | prf rewrite lemma33 ρM ρ M | lemma33 ρN ρ N = prf
  lemma  (`val V)   {ρM} {ρN} simρ
   with lemma V simρ
  ... | prf = V^[ prf ]^T^V
  lemma  (F `$ A)   {ρM} {ρN} simρ
   with lemma F simρ | lemma A simρ
  ... | simF | simA = log-sim₀^T-app simF simA
  lemma (`if B L R) {ρM} {ρN} simρ
   with lemma B simρ | lemma L simρ | lemma R simρ
  ... | simB | simL | simR  = log-sim₀^T-if simB simL simR
  lemma (`let P Q)  {ρM} {ρN} simρ
   with lemma P simρ
  ... | simP = log-sim₀^T-let simP simQ
   where
    QM = subst (Q ⟪ M ⟫) (ext₀^Env ρM) ; QN = subst (Q ⟪ N ⟫) (ext₀^Env ρN)
    simQ : ∀ {V W} → log-sim₀ V W → log-sim₀ (QM ⟨ V /var₀⟩) (QN ⟨ W /var₀⟩)
    simQ {V} {W} sVW
     with lemma Q {ρM `∙ V} {ρN `∙ W} (log-sim₀^Ext simρ sVW)
    ... | prf rewrite lemma34 (Q ⟪ M ⟫) ρM V | lemma34 (Q ⟪ N ⟫) ρN W = prf

-- Last one: logical implies contextual

lemma-2-18O : ∀ {Γ} {τ} {M N} → log-sim M N → cxt-sim {`trm} {Γ} {τ} M N
lemma-2-18O {Γ} {τ} {M} {N} sMN P
 with lemma-2-18-aux P {M} {N} sMN ([ log-sim₀^V ]^Env-refl₀ ι^Env)
... | prf = log-sim-sim₀ {`trm} sPMN
 where
  sPMN : log-sim₀^T (P ⟪ M ⟫) (P ⟪ N ⟫)
  sPMN rewrite PEq.sym (ι^Env₀ (P ⟪ M ⟫)) | PEq.sym (ι^Env₀ (P ⟪ N ⟫)) = prf

Lemma-2-18 : (f : CBV) → Set
Lemma-2-18 f = ∀ {τ} {M N} → log-sim₀ M N → cxt-sim₀ {f} {τ} M N
lemma-2-18 : ∀ {f} → Lemma-2-18 f
lemma-2-18 {f} = case f return Lemma-2-18 of λ { `val → prfV ; `trm → prfT }
 where
  prfV : Lemma-2-18 `val
  prfT : Lemma-2-18 `trm
  prfV = prfT ∘ V^[_]^T^V
  prfT = lemma-2-18O ∘ (log-sim₀-log-sim {`trm}) -- {Γ = ε}

{--------------}
{-- Summary   -}
{--------------}

-- on closed terms

cxt-sim₀→app-cxt-sim₀^T : ∀ {τ} {M N : Trm₀ τ} →
  cxt-sim₀ M N → app-cxt-sim₀ M N
cxt-sim₀→app-cxt-sim₀^T = lemma-2-6

app-cxt-sim₀→app-sim₀^T : ∀ {τ} {M N : Trm₀ τ} →
  app-cxt-sim₀ M N → app-sim₀^T {τ} M N
app-cxt-sim₀→app-sim₀^T = lemma-2-11 {`trm}

app-sim₀→log-sim₀^T : ∀ {τ} {M N : Trm₀ τ} →
  app-sim₀ M N → log-sim₀ M N
app-sim₀→log-sim₀^T = lemma-2-20 {`trm}

log-sim₀→cxt-sim₀^T : ∀ {τ} {M N : Trm₀ τ} →
  log-sim₀ M N → cxt-sim₀ M N
log-sim₀→cxt-sim₀^T = lemma-2-18 {`trm}

-- on open terms
{-
-- NB Agda and eta expansion: sometimes v. unpredictable!
-}
-- simple restatement suffices here ...
cxt-sim→app-cxt-sim^T : ∀ {Γ} {τ} {M N : Trm τ Γ} →
  cxt-sim M N → app-cxt-sim M N
cxt-sim→app-cxt-sim^T = lemma-2-6O

-- ... but here is not enough!
app-cxt-sim→app-sim^T : ∀ {Γ} {τ} {M N : Trm τ Γ} →
  app-cxt-sim M N → app-sim M N
app-cxt-sim→app-sim^T {Γ} {τ} {M} {N}  = lemma-2-11O {Γ} {τ} {M} {N}

-- nor here ...
app-sim→log-sim^T : ∀ {Γ} {τ} {M N : Trm τ Γ} →
  app-sim M N → log-sim M N
app-sim→log-sim^T {Γ} {τ} {M} {N} = lemma-2-20O {Γ} {τ} {M} {N}

-- ... but simple restatement works here
log-sim→cxt-sim^T : ∀ {Γ} {τ} {M N : Trm τ Γ} →
  log-sim M N → cxt-sim M N
log-sim→cxt-sim^T = lemma-2-18O
