{-------------------------------------}
{- Triangle for Big-step evaluation. -}
{-------------------------------------}
module tri-big-step where

open import Level as L using (Level ; _⊔_)
open import Function as F hiding (_∋_ ; _$_)

open import acmm
open import relations
open import big-step-prop
open import obs-apx
open import vcc-apx
open import asc-apx
open import sim-fusion-lemmas

{-------------------------------------}
{-- Big-step Approximation relations -}
{-------------------------------------}

-- Applicative approximation
mutual

 app-apx₀ : GRel₀^E
 app-apx₀ {`val} = app-apx₀^V
 app-apx₀ {`trm} = app-apx₀^T

 data
  app-apx₀^B : GRel₀^B where

   app-apx₀^B-b : ∀ {β} {b b'} → gnd-eqv₀^B {β} b b' →
    app-apx₀^B {β} b b'

 data
  app-apx₀^V : GRel₀^V where

   app-apx₀^V-b : ∀ {β} {b b'} → app-apx₀^B {β} b b' →
    app-apx₀^V {`b β} (`b b) (`b b')

   app-apx₀^V-λ : ∀ {σ τ} {M N} →
      (∀ U → app-apx₀^T {τ} (M ⟨ U /var₀⟩) (N ⟨ U /var₀⟩)) →
               app-apx₀^V {σ `→ τ} (`λ M) (`λ N)

 app-apx₀^T : GRel₀^T
 app-apx₀^T {τ} M N = M [ app-apx₀^V {τ} ]^T N

-- open extension of app-apx₀
App-apx : ∀ (f : CBV) → Set₁
App-apx f = ∀ {Γ} {τ} → Rel^E {f} {L.zero} {Γ} {τ}
app-apx : ∀ {f} → App-apx f
app-apx {f} = case f return App-apx of λ { `val →  apxV ; `trm → apxT  }
 where
  apxV : App-apx `val
  apxT : App-apx `trm
  apxV {Γ} {τ} = _[ apxT {Γ} {τ} ]^V_
  apxT {Γ} {τ} = _[ app-apx₀ {`trm} {τ} ]^O_

--
App-apx₀-refl : (f : CBV) → Set
App-apx₀-refl f = ∀ {τ} E → app-apx₀ {f} {τ} E E
app-apx₀-refl : ∀ {f} → App-apx₀-refl f
app-apx₀-refl {f} = case f return App-apx₀-refl of
  λ { `val →  prfV ; `trm → prfT }
 where
  prfV : App-apx₀-refl `val
  prfT : App-apx₀-refl `trm
  prfV  {`b β}  (`var ())
  prfV  {`b β}   (`b b) = app-apx₀^V-b {b = b} (app-apx₀^B-b (gnd-eqv₀^B-b b))

  prfV {σ `→ τ} (`var ())
  prfV {σ `→ τ}  (`λ M)  = app-apx₀^V-λ (λ U → prfT {τ} (M ⟨ U /var₀⟩))

  prfT {τ} = lemma-[ prfV {τ} ]^T-refl

app-apx₀^V-βV-λ : ∀ {σ τ} {M N} → (∀ U → app-apx₀^T (βV M U) (βV N U)) →
 app-apx₀^V {σ `→ τ} (`λ M) (`λ N)
app-apx₀^V-βV-λ r =
  app-apx₀^V-λ (λ U → lemma-2-10i →₁app (lemma-2-10ii (r U) →₁app))

app-apx₀^T-appT : ∀ {σ τ} {M N} →
 (∀ U → app-apx₀^T {τ} (appT M U) (appT N U)) →
 (gnd-eqv₀^T M N) → app-apx₀^T {σ `→ τ} M N

app-apx₀^T-appT {σ} {τ} r = lemma-[-]^T-gnd-eqv₀-λ {R = app-apx₀^V}
 (λ derM derN → app-apx₀^V-βV-λ (λ U → lemma-[-]^T-βV derM (r U) derN))

lemma-3-10B : ∀ {β} {V W : Val₀ (`b β)} →
  gnd-eqv₀^V {`b β} V W → app-apx₀^V {`b β} V W
lemma-3-10B (gnd-eqv₀^V-b (gnd-eqv₀^B-b b)) = app-apx₀-refl (`b b)

lemma-3-10O : ∀ {Γ} {τ} {M N} → asc-apx M N → app-apx {`trm} {Γ} {τ} M N
lemma-3-10O {Γ} {`b β} sMN ρ = lemma-[ lemma-3-10B {β} ]^T-mono (sMN ⟪- ρ -⟫)
lemma-3-10O {Γ} {σ `→ τ} {M} {N} sMN ρ =
  app-apx₀^T-appT app-apx₀-appT (sMN ⟪- ρ -⟫)
 where
  -- basic applicative setting, relative to the valuation ρ
  appT₀ : (M : Exp (σ `→ τ) Γ) (U : Val₀ σ) → Trm₀ τ
  appT₀ M U = appT (subst M ρ) U

  appP₀ : (U : Val₀ σ) → ASC⟪ Γ ⊢ σ `→ τ ⟫ τ ε
  appP₀ U = ⟪- ρ -⟫ `* U

  -- hence asc-apx₀ is closed under appT₀, modulo rewrites
  apx-appT₀ : ∀ U → asc-apx₀ (appT₀ M U) (appT₀ N U)
  apx-appT₀ U P with sMN (P ⟪∘⟫ASC appP₀ U)
  ... | prf rewrite P ⟪∘ M ⟫ASC appP₀ U | P ⟪∘ N ⟫ASC appP₀ U = prf

  app-apx₀-appT : ∀ U →
    app-apx₀^T {τ} (appT (subst M ρ) U) (appT (subst N ρ) U)
  app-apx₀-appT U with lemma-3-10O (apx-appT₀ U) ι^Env
  ... | prf rewrite ι^Env₀ (subst M ρ) | ι^Env₀ (subst N ρ)
            with    ren-sub→sub-ren U (weak {σ = σ `→ τ}) weak
                                    (ext₀^Env ι^Env) ι^Env
                                    (λ v → PEq.refl)
  ... | weak-ι^Env-comm rewrite weak-ι^Env-comm | ι^Env₀ U = prf

Lemma-3-10 : (f : CBV) → Set
Lemma-3-10 f = ∀ {τ} {M N} → asc-apx₀ M N → app-apx₀ {f} {τ} M N
lemma-3-10 : ∀ {f} → Lemma-3-10 f
lemma-3-10 {f} =
  case f return Lemma-3-10 of λ { `val →  prfV ; `trm → prfT  }
 where
  prfV : Lemma-3-10 `val
  prfT : Lemma-3-10 `trm

  prfV sMN = T^V^[ prfT sMN ]^V

  prfT {τ} {M} {N} sMN with lemma-3-10O sMN ι^Env
  ... | prf rewrite ι^Env₀ M | ι^Env₀ N = prf

-- Logical approximation
-- NB: Not an inductive definition!
log-apx₀ : GRel₀^E
log-apx₀^V : GRel₀^V
log-apx₀^T : GRel₀^T
log-apx₀ {`val} = log-apx₀^V
log-apx₀ {`trm} = log-apx₀^T

log-apx₀^V {`b β} (`var ())
log-apx₀^V {`b β}  (`b b) (`var ())
log-apx₀^V {`b β}  (`b b)  (`b b') = gnd-eqv₀^B b b'

log-apx₀^V {σ `→ τ} (`var ())
log-apx₀^V {σ `→ τ}  (`λ M) (`var ())
log-apx₀^V {σ `→ τ}  (`λ M)  (`λ N)  =
  ∀ {V W} → log-apx₀^V V W → log-apx₀^T (M ⟨ V /var₀⟩) (N ⟨ W /var₀⟩)

log-apx₀^T {τ} = _[ log-apx₀^V {τ} ]^T_

log-apx^B-refl : ∀ {β} b → log-apx₀^V {`b β} (`b b) (`b b)
log-apx^B-refl {β} b = gnd-eqv₀^B-b b

-- a useful lemma, needed in 2.18O below
Log-apx-gnd-eqv₀ : (f : CBV) → Set
Log-apx-gnd-eqv₀ f = ∀ {σ} {M N} → log-apx₀ M N → gnd-eqv₀ {f} {σ} M N
log-apx-gnd-eqv₀ : ∀ {f} → Log-apx-gnd-eqv₀ f
log-apx-gnd-eqv₀ {f} = case f return Log-apx-gnd-eqv₀ of
  λ { `val → prfV ; `trm → prfT }
 where
  prfV : Log-apx-gnd-eqv₀ `val
  prfT : Log-apx-gnd-eqv₀ `trm
  prfV {M = `var ()}
  prfV  {M = `b b} {N = `var ()}
  prfV  {M = `b b}  {N = `b b'} = gnd-eqv₀^V-b

  prfV {M = `λ M} {`var ()}
  prfV {M = `λ M} {N = `λ N} _ = gnd-eqv₀^V-λ

  prfT {σ} = lemma-[ prfV {σ} ]^T-mono

-- analogues of alternative introductions for app-apx at λs/higher type
log-apx₀-βV-λ : ∀ {σ τ} {M N} →
 (∀ {V W} → log-apx₀ V W → log-apx₀ (βV M V) (βV N W)) →
 log-apx₀^V {σ `→ τ} (`λ M) (`λ N)
log-apx₀-βV-λ r = λ U → lemma-2-10i →₁app (lemma-2-10ii (r U) →₁app)

log-apx₀-appT : ∀ {σ τ} {M N} →
 (∀ {V W} → log-apx₀ V W → log-apx₀ (appT M V) (appT N W)) →
 gnd-eqv₀ M N → log-apx₀^T {σ `→ τ} M N
log-apx₀-appT {σ} {τ} r = lemma-[-]^T-gnd-eqv₀-λ {R = log-apx₀^V}
 (λ derM derN → log-apx₀-βV-λ (λ U → lemma-[-]^T-βV derM (r U) derN))

-- now must develop fundamental lemma 2.16!
-- warm-up congruence rules: need expansion versions of lemma-2-10

log-apx₀^T-app : ∀ {σ τ} {f g} {a b} →
  log-apx₀^V {σ `→ τ} f g → log-apx₀ a b → log-apx₀ (f `$ a) (g `$ b)
log-apx₀^T-app = lemma-[-]^T-app {R = log-apx₀^V} (λ sVW sMN → sMN sVW)

log-apx₀^T-if : ∀ {σ} {b b'} {l l' r r'} → log-apx₀ b b' →
 log-apx₀ l l' → log-apx₀ r r' → log-apx₀^T {σ} (`if b l r) (`if b' l' r')
log-apx₀^T-if = lemma-[-]^T-if {R = log-apx₀^V} idB -- apx₀^B-refl-inv
 where
  idB : {b b' : ⟦ `B ⟧B} → log-apx₀ (`b b) (`b b') → b ≡ b'
  idB (gnd-eqv₀^B-b b) = PEq.refl

log-apx₀^T-let : ∀ {σ τ} {M M'} {N N'} → (log-apx₀^T {σ} M M') →
 (∀ {V W} → log-apx₀ V W → log-apx₀ (N ⟨ V /var₀⟩) (N' ⟨ W /var₀⟩)) →
 log-apx₀^T {τ} (`let M N) (`let M' N')

log-apx₀^T-let = lemma-[-]^T-let {R = log-apx₀^V}

log-apx₀^Ext : ∀ {σ} {V W : Val₀ σ} {Γ} {ρ ρ' : Env₀ Γ}
               (apxρ : ρ [ log-apx₀^V ]^Env ρ') (sVW : log-apx₀ V W) →
               (ρ `∙ V) [ log-apx₀^V ]^Env (ρ' `∙ W)
log-apx₀^Ext apxρ sVW = _∙₀^R_ {𝓔^R = log-apx₀^V} apxρ sVW

 -- fundamental definition on open terms

log-apx : ∀ {f} {Γ} {τ} → Rel^E {f} {_} {Γ} {τ}
log-apx = _O^[ log-apx₀ ]^O_

-- lifting closed to open

Log-apx₀-log-apx : (f : CBV) → Set
Log-apx₀-log-apx f = ∀ {σ} {M N} → log-apx₀ M N → log-apx {f} {ε} {σ} M N

log-apx₀-log-apx : ∀ {f} → Log-apx₀-log-apx f
log-apx₀-log-apx {f} = case f return Log-apx₀-log-apx of
  λ { `val → prfV ; `trm → prfT }
 where
  prfV : Log-apx₀-log-apx `val
  prfT : Log-apx₀-log-apx `trm
  prfV {σ} {V} {W} sVW apxρ =
    T^V^[ prfT {σ} {`val V} { `val W} V^[ sVW ]^T^V apxρ ]^V
  prfT {σ} {M} {N} sMN {ρM} {ρN} apxρ = prf
   where
    prf : log-apx₀^T (subst M ρM) (subst N ρN)
    prf rewrite ι^Env₀-lemma ρM M | ι^Env₀-lemma ρN N = sMN

-- now we begin in earnest: fundamental lemma on open terms
lemma-3-19 : ∀ {f} {Γ} {τ} (E : Exp {f} τ Γ) → log-apx E E
lemma-3-19 (`var v) apxρ = apxρ v
lemma-3-19  (`b b)  apxρ = log-apx^B-refl b

lemma-3-19  (`λ M) {ρ} {ρ'} apxρ {V} {W} sVW
 with lemma-3-19 M (log-apx₀^Ext apxρ sVW)
... | prf rewrite lemma34 M ρ V | lemma34 M ρ' W = prf

lemma-3-19   (`val V)       = V^[_]^T^V ∘ (lemma-3-19 V)
lemma-3-19   (f `$ a)  apxρ = log-apx₀^T-app F A
 where F = lemma-3-19 f apxρ ; A = lemma-3-19 a apxρ
lemma-3-19 (`if b l r) apxρ = log-apx₀^T-if B L R
 where B = lemma-3-19 b apxρ ; L = lemma-3-19 l apxρ ; R = lemma-3-19 r apxρ
lemma-3-19 (`let M N) {ρ} {ρ'} apxρ = log-apx₀^T-let prfM prfN
 where
  prfM = lemma-3-19 M apxρ
  S = subst N (ext₀^Env ρ) ; S' = subst N (ext₀^Env ρ')

  prfN : ∀ {V W} → log-apx₀ V W → log-apx₀ (S ⟨ V /var₀⟩) (S' ⟨ W /var₀⟩)
  prfN {V} {W} sVW with lemma-3-19 N (log-apx₀^Ext apxρ sVW)
  ... | prf rewrite lemma34 N ρ V | lemma34 N ρ' W = prf

-- Ground reflexivity is then a trivial corollary.
Log-apx₀-refl : (f : CBV) → Set
Log-apx₀-refl f = ∀ {τ} E → log-apx₀ {f} {τ} E E
log-apx₀-refl : ∀ {f} → Log-apx₀-refl f
log-apx₀-refl {f} = case f return Log-apx₀-refl of
  λ { `val →  prfV ; `trm → prfT }
 where
  prfV : Log-apx₀-refl `val
  prfT : Log-apx₀-refl `trm
  prfV {`b β} (`var ())
  prfV {`b β}  (`b b) = log-apx^B-refl {β} b

  prfV {σ `→ τ} (`var ())
  prfV {σ `→ τ}  (`λ M) sVW = lemma-3-19 M (_∙₀^R_ {𝓔^R = E^R} rel sVW)
    where
      E^R = λ {τ} → log-apx₀^V {τ} 
      rel : ι^Env [ E^R ]^Env ι^Env
      rel ()

  prfT {τ} = lemma-[ prfV {τ} ]^T-refl

-- Lemma 2.20 follows from the following generalisation of transitivity, plus
-- reflexivity.

Lemma-3-20 : (f : CBV) → Set
Lemma-3-20 f = ∀ {τ} {M N P} →
  app-apx₀ M N → log-apx₀ N P → log-apx₀ {f} {τ} M P
lemma-3-20 : ∀ {f} → Lemma-3-20 f
lemma-3-20 {f} = case f return Lemma-3-20 of
  λ { `val →  prfV ; `trm → prfT  }
 where
  prfV : Lemma-3-20 `val
  prfT : Lemma-3-20 `trm
  prfV  {`b β} {`var ()}
  prfV  {`b β}  {`b .b} (app-apx₀^V-b (app-apx₀^B-b (gnd-eqv₀^B-b b))) r = r

  prfV {σ `→ τ} {`λ M} {`λ N} {`var ()} (app-apx₀^V-λ l) r
  prfV {σ `→ τ} {`λ M} {`λ N}  {`λ P}   (app-apx₀^V-λ l) r {V}
   = λ sMN → prfT (l V) (r sMN)

  prfT {τ} = lemma-[ prfV {τ} ]^T-trans

lemma-3-21 : ∀ {f} {τ} {M N} → app-apx₀ M N → log-apx₀ {f} {τ} M N
lemma-3-21 {f} {τ} {M} {N} sMN = lemma-3-20 {f} {τ} sMN (log-apx₀-refl N)

-- now use fundamental lemma 2.16, and generalised transitivity above,
-- to conclude on open terms
lemma-3-21O : ∀ {Γ} {τ} {M N : Trm τ Γ} → app-apx M N → log-apx M N
lemma-3-21O {Γ} {τ} {M} {N} sMN {ρM} {ρN} apxρ =
  lemma-3-20 {`trm} (sMN ρM) (lemma-3-19 N apxρ)

-- Now, Lemma 3.22, done using Ian's argument.

lemma-3-22 : ∀ {f} {Γ Δ} {τ υ} (P : VSC⟪ Γ ⊢ τ ⟫ {f} υ Δ) →
 ∀ {M N} → log-apx M N → log-apx (P ⟪ M ⟫) (P ⟪ N ⟫)

lemma-3-22 (`exp E)          _           apxρ = lemma-3-19 E apxρ

lemma-3-22  (`λ P) {M} {N} sMN {ρM} {ρN} apxρ {V} {W} sVW
 with lemma-3-22 P {M} {N} sMN {ρM `∙ V} {ρN `∙ W} (log-apx₀^Ext apxρ sVW)
... | prf rewrite lemma34 (P ⟪ M ⟫) ρM V | lemma34 (P ⟪ N ⟫) ρN W = prf

lemma-3-22   ⟪- ρ -⟫   {M} {N} sMN {ρM} {ρN} apxρ
 with sMN {ρM *-Sub ρ} {ρN *-Sub ρ} (λ {σ} v → lemma-3-19 (var ρ {σ} v) apxρ)
... | prf rewrite lemma33 ρM ρ M | lemma33 ρN ρ N = prf

lemma-3-22   (`val P)  {M} {N} sMN {ρM} {ρN} apxρ
 with lemma-3-22 P {M} {N} sMN {ρM} {ρN} apxρ
... | prf = V^[ prf ]^T^V

-- now it's just congruence rules (that's Ian's point)
lemma-3-22   (F `$ A)  {M} {N} sMN {ρM} {ρN} apxρ
 = log-apx₀^T-app (lemma-3-22 F sMN apxρ) (lemma-3-22 A sMN apxρ)

lemma-3-22 (`if B L R) {M} {N} sMN {ρM} {ρN} apxρ
 = log-apx₀^T-if (lemma-3-22 B sMN apxρ)
  (lemma-3-22 L sMN apxρ) (lemma-3-22 R sMN apxρ)

lemma-3-22  (`let P Q) {M} {N} sMN {ρM} {ρN} apxρ
 = log-apx₀^T-let (lemma-3-22 P sMN apxρ) prfQ
  where
   QM = subst (Q ⟪ M ⟫) (ext₀^Env ρM) ; QN = subst (Q ⟪ N ⟫) (ext₀^Env ρN)
   prfQ : ∀ {V W} → log-apx₀ V W → log-apx₀ (QM ⟨ V /var₀⟩) (QN ⟨ W /var₀⟩)
   prfQ {V} {W} sVW
    with lemma-3-22 Q {M} {N} sMN {ρM `∙ V} {ρN `∙ W}
                        (log-apx₀^Ext apxρ sVW)
   ... | prf rewrite lemma34 (Q ⟪ M ⟫) ρM V | lemma34 (Q ⟪ N ⟫) ρN W = prf

-- Last one: logical implies observational

lemma-3-23O : ∀ {Γ} {τ} {M N} → log-apx M N → vsc-apx {`trm} {Γ} {τ} M N
lemma-3-23O {Γ} {τ} {M} {N} sMN P
 with lemma-3-22 P {M} {N} sMN ([ log-apx₀^V ]^Env-refl₀ ι^Env)
... | prf = log-apx-gnd-eqv₀ {`trm} sPMN
 where
  sPMN : log-apx₀^T (P ⟪ M ⟫) (P ⟪ N ⟫)
  -- NB: The order of rewrites here makes a difference: ι^Env₀ *after*
  -- ι^Env₀-lemma!
  sPMN rewrite ι^Env₀-lemma (mkEnv (λ {σ} → `var)) (P ⟪ M ⟫) |
               PEq.sym (ι^Env₀ (P ⟪ M ⟫)) |
               ι^Env₀-lemma (mkEnv (λ {σ} → `var)) (P ⟪ N ⟫) |
               PEq.sym (ι^Env₀ (P ⟪ N ⟫)) = prf

Lemma-3-23 : (f : CBV) → Set
Lemma-3-23 f = ∀ {τ} {M N} → log-apx₀ M N → vsc-apx₀ {f} {τ} M N
lemma-3-23 : ∀ {f} → Lemma-3-23 f
lemma-3-23 {f} = case f return Lemma-3-23 of λ { `val → prfV ; `trm → prfT }
 where
  prfV : Lemma-3-23 `val
  prfT : Lemma-3-23 `trm
  prfV = prfT ∘ V^[_]^T^V
  prfT = lemma-3-23O ∘ (log-apx₀-log-apx {`trm}) -- {Γ = ε}

