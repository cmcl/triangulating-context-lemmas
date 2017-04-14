{------------------------}
{- Big-step properties  -}
{------------------------}
module big-step-prop where

open import Level as L using (Level ; _⊔_)
open import Data.Bool renaming (true to tt ; false to ff)
open import Data.Product hiding (map)
open import Function as F hiding (_∋_ ; _$_)
open import Relation.Binary.PropositionalEquality as PEq using (_≡_)

open import lambda-fg
open import acmm
open import relations

lemma-2-1 : {τ : Ty} {M : Trm₀ τ} {U V : Val₀ τ} → M ⇓ U → M ⇓ V → U ≡ V
lemma-2-1 ⇓val ⇓val = PEq.refl
lemma-2-1 (⇓if-tt derU) (⇓if-tt derV) = lemma-2-1 derU derV
lemma-2-1 (⇓if-ff derU) (⇓if-ff derV) = lemma-2-1 derU derV
lemma-2-1 (⇓app derU) (⇓app derV)     = lemma-2-1 derU derV
lemma-2-1 (⇓let derU derU') (⇓let derV derV')
 rewrite lemma-2-1 derU derV | lemma-2-1 derU' derV' = PEq.refl

lemma-2-3i : {τ : Ty} {M N : Trm₀ τ} {V : Val₀ τ} →
             (dev : M ⇓ V) → (red : M →₁ N) → N ⇓ V

lemma-2-3i (⇓if-tt dev)      →₁if         = dev
lemma-2-3i (⇓if-ff dev)      →₁if         = dev
lemma-2-3i (⇓app dev)        →₁app        = dev
{-
lemma-2-3i (⇓let (⇓val) dev) →₁letV = dev
lemma-2-3i (⇓let devM devN) (→₁letT redM) = ⇓let (lemma-2-3i devM redM) devN
-}

→₁letTi : {σ τ : Ty} {N : (σ ⊢ Trm τ) _} {M M' : _} {V : Val₀ _} →
          (der : `let M N ⇓ V) → (red : M →₁ M') → `let M' N ⇓ V

→₁letTi (⇓let derM derN) red = ⇓let (lemma-2-3i derM red) derN

lemma-2-3ii : {τ : Ty} {M N : Trm₀ τ} {V : Val₀ τ} →
              (red : M →₁ N) → (dev : N ⇓ V) → M ⇓ V

lemma-2-3ii (→₁if {b = tt}) = ⇓if-tt
lemma-2-3ii (→₁if {b = ff}) = ⇓if-ff
lemma-2-3ii →₁app           = ⇓app
{-
lemma-2-3ii dev →₁letV          = ⇓let ⇓val dev
lemma-2-3ii (⇓let devM devN) (→₁letT redM) = ⇓let (lemma-2-3ii devM redM) devN
-}

→₁letTii : {σ τ : Ty} {N : (σ ⊢ Trm τ) _} {M M' : _} {V : Val₀ _} →
           (red : M →₁ M') → (der : `let M' N ⇓ V) → `let M N ⇓ V

→₁letTii red (⇓let derM derN) = ⇓let (lemma-2-3ii red derM) derN

{----------------------------}
{-- Generic Lemmas on [_]^T -}
{----------------------------}

-- Lemmas regarding Val to Trm relation transformer
lemma-[_]^T-refl : {ℓ^V : Level} {τ : Ty} {R : GRel^V {ℓ^V} {τ}}
  (r : (V : Val₀ τ) → R V V) → (M : Trm₀ τ) → M [ R ]^T M
lemma-[ r ]^T-refl M {U = U} der = U , der , r U

lemma-[_]^T-trans : {ℓ^V : Level} {τ : Ty} {R S T : GRel^V {ℓ^V} {τ}}
  (t : {M N P : Val₀ τ} → R M N → S N P → T M P) →
  {M N P : Trm₀ τ} → M [ R ]^T N → N [ S ]^T P → M [ T ]^T P
lemma-[ t ]^T-trans M[R]^TN N[S]^TP derM with M[R]^TN derM
... | _ , derN , rUV with N[S]^TP derN
... | _ , derP , sVW = _ , derP , t rUV sVW

lemma-[_]^T-mono : {ℓ^V : Level} {τ : Ty} {R S : GRel^V {ℓ^V} {τ}}
  (m : {M N : Val₀ τ} → R M N → S M N) →
  {M N : Trm₀ τ} → M [ R ]^T N → M [ S ]^T N
lemma-[ m ]^T-mono M[R]^TN {V} derM with M[R]^TN derM
... | _ , derN , rVW = _ , derN , m rVW

-- Trm relation transformer left/right respects primitive reduction.

lemma-2-10i : {ℓ^V : Level} {τ : Ty} {R : GRel^V {ℓ^V} {τ}}
  {M N P : Trm₀ τ} → M →₁ P → (M [ R ]^T N) → P [ R ]^T N
lemma-2-10i red r = r ∘ (lemma-2-3ii red)

lemma-2-10i-exp : {ℓ^V : Level} {τ : Ty} {R : GRel^V {ℓ^V} {τ}}
  {M N P : Trm₀ τ} → P →₁ M → (M [ R ]^T N) → P [ R ]^T N
lemma-2-10i-exp red r der = r (lemma-2-3i der red)

lemma-2-10ii : {ℓ^V : Level} {τ : Ty} {R : GRel^V {ℓ^V} {τ}}
  {M N P : Trm₀ τ} → (M [ R ]^T N) → N →₁ P → M [ R ]^T P
lemma-2-10ii r red der with r der
... | V , derM , rUV = V , lemma-2-3i derM red , rUV

lemma-2-10ii-exp : {ℓ^V : Level} {τ : Ty} {R : GRel^V {ℓ^V} {τ}}
  {M N P : Trm₀ τ} → (M [ R ]^T N) → P →₁ N → M [ R ]^T P
lemma-2-10ii-exp r red der with r der
... | V , derM , rUV = V , lemma-2-3ii red derM , rUV

lemma-[-]^T-βV : {ℓ^V : Level} {τ : Ty} {R : GRel^V {ℓ^V} {τ}} →
 ∀ {σ} {P Q : Trm₀ (σ `→ τ)} {M N} {V W} →
 P ⇓ `λ M → appT P V [ R ]^T appT Q W → Q ⇓ `λ N →
 (βV M V) [ R ]^T (βV N W)
lemma-[-]^T-βV derM r derN (⇓app derV)
 with r (⇓let derM (⇓app derV))
... | U , ⇓let derQ (⇓app derU) , simU
 rewrite `λ-inj (lemma-2-1 derN derQ) = U , ⇓app derU , simU

-- congruence rules

lemma-[-]^T-app : {ℓ^V : Level} {R : {τ : Ty} → GRel^V {ℓ^V} {τ}} →
 ∀ {σ τ} →
 (R-λ : ∀ {M N} {V W} → R {σ} V W → R {σ `→ τ} (`λ M) (`λ N) →
  M ⟨ V /var₀⟩ [ R {τ} ]^T N ⟨ W /var₀⟩) →
 ∀ {f g} {a b} → R {σ `→ τ} f g → R {σ} a b → (f `$ a) [ R {τ} ]^T (g `$ b)
lemma-[-]^T-app R-λ {`var ()}
lemma-[-]^T-app R-λ  {`λ M} {`var ()}
lemma-[-]^T-app R-λ  {`λ M}  {`λ N} {V} {W} rMN rVW =
 lemma-2-10i-exp →₁app (lemma-2-10ii-exp (R-λ {M} {N} rVW rMN) →₁app)

lemma-[-]^T-if : {ℓ^V : Level} {R : {τ : Ty} → GRel^V {ℓ^V} {τ}} →
 (R-B : ∀ {b b' : ⟦ `B ⟧B} → R (`b b) (`b b') → b ≡ b') →
 ∀ {σ} {B C M N P Q} → R {`b `B} B C → M [ R {σ} ]^T P → N [ R {σ} ]^T Q →
 (`if B M N) [ R {σ} ]^T (`if C P Q)
lemma-[-]^T-if R-B {B = `var ()}
lemma-[-]^T-if R-B  {B = `b b} {`var ()}
lemma-[-]^T-if R-B  {B = `b b} {C = `b b'} rBC rMP rNQ with R-B rBC
lemma-[-]^T-if R-B  {B = `b tt} {C = `b .tt} rBC rMP rNQ | PEq.refl =
  lemma-2-10i-exp →₁if (lemma-2-10ii-exp rMP →₁if)
lemma-[-]^T-if R-B  {B = `b ff} {C = `b .ff} rBC rMP rNQ | PEq.refl =
  lemma-2-10i-exp →₁if (lemma-2-10ii-exp rNQ →₁if)

lemma-[-]^T-let : {ℓ^V : Level} {R : {τ : Ty} → GRel^V {ℓ^V} {τ}} →
 ∀ {σ τ} {M N P Q} → M [ R {σ} ]^T P →
 (∀ {V W} → R {σ} V W → N ⟨ V /var₀⟩ [ R {τ} ]^T Q ⟨ W /var₀⟩) →
 `let M N [ R ]^T `let P Q
lemma-[-]^T-let simM simN (⇓let derM derN) with simM derM
... | W , derW , rVW with simN rVW derN
... | U , derU , rU = U , ⇓let derW derU , rU
