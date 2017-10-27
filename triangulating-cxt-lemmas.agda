module triangulating-cxt-lemmas where

open import Function as F hiding (_∋_ ; _$_)

open import lambda-fg
open import obs-apx
open import vcc-apx
open import asc-apx
open import tri-big-step
open import ciu-apx
open import tri-frm-stk

{--------------------------------}
{-- Big-step triangle Summary  --}
{--------------------------------}

-- on open terms
vsc-apx→app-apx^T : ∀ {Γ} {τ} {M N : Trm τ Γ} →
  vsc-apx M N → app-apx M N
vsc-apx→app-apx^T = (lemma-3-10O ∘ vcc-apx→asc-apx^T) ∘ vsc-apx→vcc-apx^T

app-apx→log-apx^T : ∀ {Γ} {τ} {M N : Trm τ Γ} →
  app-apx M N → log-apx M N
app-apx→log-apx^T {Γ} {τ} {M} {N} = lemma-3-21O {Γ} {τ} {M} {N}

log-apx→vsc-apx^T : ∀ {Γ} {τ} {M N : Trm τ Γ} →
  log-apx M N → vsc-apx M N
log-apx→vsc-apx^T = lemma-3-23O

-- on closed terms
vsc-apx₀→app-apx₀^T : ∀ {τ} {M N : Trm₀ τ} → vsc-apx₀ M N → app-apx₀^T {τ} M N
vsc-apx₀→app-apx₀^T =
    (lemma-3-10 {`trm} ∘ vcc-apx₀→asc-apx₀^T) ∘ vsc-apx₀→vcc-apx₀^T

app-apx₀→log-apx₀^T : ∀ {τ} {M N : Trm₀ τ} → app-apx₀ M N → log-apx₀ M N
app-apx₀→log-apx₀^T = lemma-3-21 {`trm}

log-apx₀→vsc-apx₀^T : ∀ {τ} {M N : Trm₀ τ} → log-apx₀ M N → vsc-apx₀ M N
log-apx₀→vsc-apx₀^T = lemma-3-23 {`trm}

{-----------------------------------}
{-- Frame stack triangle Summary  --}
{-----------------------------------}

-- on open terms

vsc-apx→app-frm-apx^T : ∀ {Γ} {τ} {M N : Trm τ Γ} →
  vsc-apx M N → app-frm-apx M N
vsc-apx→app-frm-apx^T = ciu-apx→app-frm-apx ∘ vsc-apx→ciu-apx^T

app-frm-apx→log-frm-apx^T : ∀ {Γ} {τ} {M N : Trm τ Γ} →
  app-frm-apx M N → log-frm-apx M N
app-frm-apx→log-frm-apx^T {Γ} {τ} {M} {N} = lemma-4-17O {Γ} {τ} {M} {N}

log-frm-apx→vsc-apx^T : ∀ {Γ} {τ} {M N : Trm τ Γ} →
  log-frm-apx M N → vsc-apx M N
log-frm-apx→vsc-apx^T = lemma-4-15O

-- on closed terms

vsc-apx₀→app-frm-apx₀^T : ∀ {τ} {M N : Trm₀ τ} →
  vsc-apx₀ M N → app-frm-apx₀ M N
vsc-apx₀→app-frm-apx₀^T = ciu-apx₀→app-frm-apx₀ ∘ (vsc-apx→ciu-apx^T {ε})

app-frm-apx₀→log-frm-apx₀^T : ∀ {τ} {M N : Trm₀ τ} →
  app-frm-apx₀ M N → log-frm-apx₀ M N
app-frm-apx₀→log-frm-apx₀^T = lemma-4-17 {`trm}

log-frm-apx₀→vsc-apx₀^T : ∀ {τ} {M N : Trm₀ τ} →
  log-frm-apx₀ M N → vsc-apx₀ M N
log-frm-apx₀→vsc-apx₀^T = lemma-4-15 {`trm}
