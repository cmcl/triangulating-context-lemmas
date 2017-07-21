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

renC : ∀ {f} {Γ Δ Δ'} {σ τ} → VCC⟪ Γ ⊢ σ ⟫ {f} τ Δ → Δ ⊆ Δ' →
  VCC⟪ Γ ⊢ σ ⟫ {f} τ Δ'
renC (`λ M) ρ = `λ (renC M (ext₀^Var ρ))
renC (`exp M) ρ = `exp (ρ *-Var M)
renC ⟪- r -⟫ ρ = ⟪- trans^Var r ρ -⟫
renC (`val P) = `val ∘ (renC P)
renC (F `$ A) ρ = (renC F ρ) `$ (renC A ρ)
renC (`if B L R) ρ = `if (renC B ρ) (renC L ρ) (renC R ρ)
renC (`let M N) ρ = `let (renC M ρ) (renC N (ext₀^Var ρ))

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

renC-VCC : ∀ {f} {Γ Δ Ξ} {σ τ} → (P : VCC⟪ Γ ⊢ σ ⟫ {f} τ Δ) →
 {r r' : Δ ⊆ Ξ} → (∀ {τ} v → var r {τ} v ≡ var r' v) → renC P r ≡ renC P r'
renC-VCC P eq = {!!}

ren-ren : ∀ {f} {Γ Δ Ξ Ω} {σ τ} →
  (P : VCC⟪ Γ ⊢ σ ⟫ {f} τ Δ) → (r1 : Δ ⊆ Ξ) → (r2 : Ξ ⊆ Ω) →
  renC (renC P r1) r2 ≡ renC P (trans^Var r1 r2)
ren-ren (`λ P) r1 r2 with renC-VCC P (pop!-trans {inc₁ = r1} {inc₂ = r2})
... | ren-eq rewrite ren-eq |
                     ren-ren P (ext₀^Var r1) (ext₀^Var r2) = PEq.refl
ren-ren (`exp x) r1 r2 = {!!}
ren-ren ⟪- x -⟫ r1 r2 = {!!}
ren-ren (`val P) r1 r2 = {!!}
ren-ren (P `$ P₁) r1 r2 = {!!}
ren-ren (`if P P₁ P₂) r1 r2 = {!!}
ren-ren (`let P x) r1 r2 = {!!}

infixl 7 _,,_

_,,_ : Cx → Cx → Cx
Γ ,, ε = Γ
Γ ,, (Δ ∙ τ) = (Γ ∙ τ) ,, Δ

push : ∀ {Γ Δ Ξ} → Γ ⊨ Δ → Γ ,, Ξ ⊨ Δ ,, Ξ
var (push ρ) v = {!!}
--var (push {ε} ρ) v = var ρ v
--var (push {Γ ∙ τ} ρ) ze = `var ze
--var (push {Γ ∙ τ} ρ) (su v) = weak *-Var (var (push {Γ} ρ) v)

{-
-push-id : ∀ {Γ Δ Ξ} {σ} {v : Var σ Γ} (ρ : Δ ⊨ Ξ) →
-  var (push {Γ} ρ) v ≡ `var v
-push-id ρ = {!!}
-}

ren-bar : ∀ {f} {Γ Δ Ξ Ω} {σ τ ω} →
  (P : VCC⟪ Γ ,, Ξ ⊢ σ ⟫ {f} τ (Δ ,, Ξ)) → (V : Val ω Ω) →
  (M : Trm σ ((Γ ,, Ξ) ∙ ω)) → (r : Δ ,, Ξ ⊆ Ω ,, Ξ) → (rV : Ω ⊆ Γ ,, Ξ) →
  (prf : ∀ {Γ Δ Ξ} {σ} → Γ ,, Ξ ⊆ Δ ,, Ξ → (Γ ,, Ξ) ∙ σ ⊆ Δ ∙ σ ,, Ξ) →
  subst (renC (barC P) (prf {σ = ω} r) ⟪ M ⟫VCC) (push {Ξ = Ξ} (ι^Env {Ω} `∙ V)) ≡
    (renC P r) ⟪ M ⟨ rV *-Var V /var₀⟩ ⟫VCC
ren-bar P V M r rV prf = {!!}
{-
subst-inst-comm : ∀ {f} {Γ Δ Ξ} {σ τ ω} →
  (P : VCC⟪ Γ ⊢ σ ⟫ {f} τ Δ) → (V : Val ω Ξ) → (M : Trm σ (Γ ∙ ω))
  (r1 : Ξ ⊆ Δ) → (r2 : Ξ ⊆ Γ) → (r3 : Γ ⊆ Δ) →
  (barC- P) ⟪ M ⟫VCC ⟨ r1 *-Var V /var₀⟩ ≡ P ⟪ M ⟨ r2 *-Var V /var₀⟩ ⟫VCC
subst-inst-comm {ω = ω} (`λ P) V M r1 r2 = {!renC (barC {σ = ω} P) swp!}
subst-inst-comm (`exp E) V M r1 r2 = ? --weak-sub (r1 *-Var V) E
subst-inst-comm ⟪- r -⟫ V M r1 r2 = {!!}
subst-inst-comm (`val P) V M r1 r2
  rewrite subst-inst-comm P V M r1 r2 = PEq.refl
subst-inst-comm (F `$ A) V M r1 r2
  rewrite subst-inst-comm F V M r1 r2 |
          subst-inst-comm A V M r1 r2 = PEq.refl
subst-inst-comm (`if B L R) V M r1 r2
  rewrite subst-inst-comm B V M r1 r2 | subst-inst-comm L V M r1 r2 |
          subst-inst-comm R V M r1 r2 = PEq.refl
subst-inst-comm (`let P Q) V M r1 r2 = {!!}
-}
lemma-2-6O-VCC : ∀ {Γ} {τ} {M N} → vcc-sim M N →
  app-cxt-sim {`trm} {Γ} {τ} M N
lemma-2-6O-VCC {Γ} {`b β} = vcc-sim→sim^T
lemma-2-6O-VCC {Γ} {σ `→ τ} {M} {N} sMN ρ = (vcc-sim→sim^T sMN ρ) , {!!}
 where
  -- basic applicative setting, relative to the valuation ρ
  appT₀ : (M : Exp (σ `→ τ) Γ) (U : Val₀ σ) → Trm₀ τ
  appT₀ M U = appT (subst M ρ) U


  appP : ∀ {Γ} {σ τ} → (U : Val σ Γ) → VCC⟪ Γ ⊢ σ `→ τ ⟫ τ Γ
  appP U = `let ⟪- refl^Var -⟫ (`exp (Val→Spine U))

  app-βV : (U : Val σ Γ) → (M : Trm (σ `→ τ) Γ) →
    (VCC-sub (appP U) ρ ⟪ M ⟫VCC) →βV subst ((appP U) ⟪ M ⟫VCC) ρ
  app-βV U M rewrite VCC-betaV ρ M (appP U) = {!!}

  -- hence vcc-sim₀ is closed under appT₀, modulo rewrites
  sim-appT₀ : ∀ U → vcc-sim₀ (appT₀ M U) (appT₀ N U)
  sim-appT₀ U P = {!P ⟪ (appP U) ⟪ subst M ρ ⟫VCC ⟫VCC!}
 -- with
 --  ... | prf rewrite P ⟪∘ M ⟫VCC appP₀ U = {!!}

  -- and hence likewise, finally, app-cxt-sim₀ itself,
  -- by IH at type τ (via dummy valuation ι^Env, more rewrites)
  lemma2-6-appT₀ : ∀ U → app-cxt-sim₀ (appT₀ M U) (appT₀ N U)
  lemma2-6-appT₀ U = {!lemma-2-6O-VCC!}

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
