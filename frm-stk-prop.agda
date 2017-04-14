{--------------------------------}
{-- Properties of frame stacks. -}
{--------------------------------}
module frm-stk-prop where

open import Data.Product hiding (map)
open import Function as F hiding (_∋_ ; _$_)
open import Relation.Binary.PropositionalEquality as PEq using (_≡_)

open import lambda-fg
open import acmm
open import relations
open import big-step-prop
open import obs-apx

letF : ∀ {τ σ} (S : Frm τ σ) (M : Trm₀ σ) → Trm₀ τ
letF   Id    M = M
letF (S ∙ N) M = letF S (`let M N)

⇓letF-lemma : ∀ {σ τ} (S : Frm τ σ) →
 (∀ {M} {U} → letF S M ⇓ U → ∃ λ V → M ⇓ V × letF S (`val V) ⇓ U)
 ×
 (∀ {M} {V} {U} (derV : M ⇓ V) → (derU : letF S (`val V) ⇓ U) → letF S M ⇓ U)

⇓letF-lemma   Id  = prfL , prfR
  where prfL : ∀ {M} {U} → M ⇓ U → ∃ λ V → M ⇓ V × (`val V) ⇓ U
        prfL {U = U} der = U , der , ⇓val

        prfR : ∀ {M} {V U} → M ⇓ V → `val V ⇓ U → M ⇓ U
        prfR der ⇓val = der

⇓letF-lemma (S ∙ N) with ⇓letF-lemma S
... | ihL , ihR = prfL , prfR
 where
  prfL : ∀ {M} {U} → letF S (`let M N) ⇓ U →
           ∃ λ V → M ⇓ V × letF S (letV V N) ⇓ U
  prfL der with ihL der
  ... | _ , ⇓let {V = V} derM derN , derU =
    V , derM , ihR (⇓let ⇓val derN) derU

  prfR : ∀ {M} {V} {U} → M ⇓ V → letF S (letV V N) ⇓ U → letF S (`let M N) ⇓ U
  prfR derM der with ihL der
  ... | W , ⇓let ⇓val derN , derU = ihR (⇓let derM derN) derU

-- analogues of →₁letT/→₁letTi(i), generalised to letF S prefixes...
→₁letFi : ∀ {σ τ} {S : Frm τ σ} {M M' : _} {U : Val₀ _} →
          (der : letF S M ⇓ U) → (red : M →₁ M') → letF S M' ⇓ U
→₁letFi  {S = Id}   der red = lemma-2-3i der red
→₁letFi {S = S ∙ N} der red with ⇓letF-lemma S
... | prfL , prfR           with prfL der
... | _ , derMN , derU      = prfR (→₁letTi derMN red) derU

→₁letFii : ∀ {σ τ} {S : Frm τ σ} {M M' : _} {U : Val₀ _} →
          (red : M →₁ M') → (der : letF S M' ⇓ U) → letF S M ⇓ U
→₁letFii  {S = Id}   red der = lemma-2-3ii red der
→₁letFii {S = S ∙ N} red der with ⇓letF-lemma S
... | prfL , prfR            with prfL der
... | _ , derMN , derU       = prfR (→₁letTii red derMN) derU

-- analogue of ↓letV, generalised to letF S prefixes...
⇓letF-val : ∀ {σ τ υ} {S : Frm υ τ} {N : (σ ⊢ Trm τ) _} {V} {U} →
 letF S (N ⟨ V /var₀⟩) ⇓ U → letF (S ∙ N) (`val V) ⇓ U
⇓letF-val  {S = Id}   der       = ⇓let ⇓val der
⇓letF-val {S = S ∙ N} der with ⇓letF-lemma S
... | prfL , prfR         with prfL der
... | _ , ⇓let derN derW , derU = prfR (⇓let (⇓let ⇓val derN) derW) derU

-- first half of ⇓letF-lemma is an analogue of standardisation
⇓letF-standard : ∀ {σ τ} {S : Frm τ σ} {M} {U} →
 letF S M ⇓ U → ∃ λ V → M ⇓ V × letF S (`val V) ⇓ U
⇓letF-standard {S = S} der with ⇓letF-lemma S
... | prfL , _ = prfL der

↓letF-unwind-lemma : ∀ {σ τ} (S : Frm τ σ) {M} {U} →
                     Id , letF S M ↓ U → S , M ↓ U
↓letF-unwind-lemma   Id    der = der
↓letF-unwind-lemma (S ∙ N) der with ↓letF-unwind-lemma S der
... | ↓red () prf
... | ↓letT prf = prf

↓letV-lemma : ∀ {σ} {M} {V} (derV : M ⇓ V) →
 ∀ {τ} {U} {S : Frm τ σ} → S , `val V ↓ U → S , M ↓ U
↓letV-lemma ⇓val             = id
↓letV-lemma (⇓if-tt der)     = ↓red →₁if ∘ (↓letV-lemma der)
↓letV-lemma (⇓if-ff der)     = ↓red →₁if ∘ (↓letV-lemma der)
↓letV-lemma (⇓app der)       = ↓red →₁app ∘ (↓letV-lemma der)
↓letV-lemma (⇓let derM derN) =
  ↓letT ∘ (↓letV-lemma derM) ∘ ↓letV ∘ (↓letV-lemma derN)

corollary : ∀ {τ} {M} {V} → M ⇓ V → (Id {τ}) , M ↓ V
corollary der = ↓letV-lemma der ↓val

corollaryF : ∀ {τ υ} {S : Frm υ τ} {M} {U} → letF S M ⇓ U → S , M ↓ U
corollaryF {S = S} = (↓letF-unwind-lemma S) ∘ corollary

lemmaF : ∀ {τ υ} {S : Frm υ τ} {M} {U} → S , M ↓ U → letF S M ⇓ U
lemmaF ↓val                    = ⇓val
lemmaF {S = S} (↓red red der) = →₁letFii {S = S} red (lemmaF der)
lemmaF {S = S ∙ N} (↓letV {V = V} der)
 with ⇓letF-lemma S
... | prfL , prfR
 with prfL {M = letV V N} (⇓letF-val {S = S} (lemmaF der))
... | _ , ⇓let _ derN , derU  = prfR (⇓let ⇓val derN) derU
lemmaF (↓letT der)             = lemmaF der

↓standard : ∀ {τ υ} {S : Frm υ τ} {M} {U} → S , M ↓ U →
            ∃ λ V → Id , M ↓ V × S , `val V ↓ U
↓standard {S = S} der with ⇓letF-lemma S
... | prfL , prfR with prfL (lemmaF der)
... | V , derM , derU = V , corollary derM , corollaryF derU

letF-cxt : ∀ {Γ} {τ σ ω} (S : Frm τ σ) (P : Cxt⟪ Γ ⊢ ω ⟫ {`trm} σ ε) →
           Cxt⟪ Γ ⊢ ω ⟫ {`trm} τ ε
letF-cxt   Id    P = P
letF-cxt (S ∙ N) P = letF-cxt S (`let P (`exp N))

letF-⟪_⟫ : ∀ {Γ} {τ σ ω} (M : Trm σ Γ) (S : Frm τ ω) (P : Cxt⟪ Γ ⊢ σ ⟫ ω ε) →
           (letF-cxt S P) ⟪ M ⟫ ≡ letF S (P ⟪ M ⟫)
letF-⟪ M ⟫ Id P = PEq.refl
letF-⟪ M ⟫ (S ∙ N) P rewrite letF-⟪ M ⟫ S (`let P (`exp N)) = PEq.refl
