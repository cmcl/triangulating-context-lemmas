{---------------------------------------------}
{-- Contexts and observational approximation -}
{---------------------------------------------}
module vcc-apx where

open import Level as L using (Level ; _⊔_)
open import Function as F hiding (_∋_ ; _$_)

open import acmm
open import relations
open import big-step-prop
open import obs-apx
open import sim-fusion-lemmas

-- the null weakening/renaming 

Ren₀ : ∀ {Γ} → ε ⊆ Γ
var Ren₀ ()

-- generalities on non-empty (ground) substitutions

succ : ∀ {Γ Δ} {τ} → Γ ∙ τ ⊨ Δ → Γ ⊨ Δ
var (succ ρ) v = var ρ (su v)

zero : ∀ {Γ Δ} {τ} → Γ ∙ τ ⊨ Δ → Val τ Δ
zero ρ = var ρ ze

cons-rho : ∀ {Γ Δ} {σ} (ρ : Γ ∙ σ ⊨ Δ) →
 ∀ {τ} v → var (succ ρ `∙ zero ρ) v ≡ var ρ {τ} v 
cons-rho ρ ze = PEq.refl
cons-rho ρ (su v) = PEq.refl

ren₀-zero : ∀ {Γ} {τ} → Env₀ (Γ ∙ τ) → Val τ Γ 
ren₀-zero ρ = Ren₀ *-Var zero ρ 

sub₀-zero : ∀ {Γ} {τ} → Env₀ (Γ ∙ τ) → Γ ∙ τ ⊨ Γ
sub₀-zero ρ = ι^Env `∙ ren₀-zero ρ

zero* : ∀ {Γ} {σ τ} → Env₀ (Γ ∙ τ) → Trm σ (Γ ∙ τ) → Trm σ Γ 
zero* ρ M =  M ⟨ ren₀-zero ρ /var₀⟩

succ-ren₀-zero : ∀ {Γ} {τ} (ρ : Env₀ (Γ ∙ τ)) →
                 ((succ ρ) *-Val (ren₀-zero ρ)) ≡ zero ρ
succ-ren₀-zero ρ = ι^Var^Env-lemma-aux (zero ρ) Ren₀ (succ ρ) (λ ())

subst-succ : ∀ {Γ} {σ τ} → (ρ : Env₀ (Γ ∙ τ)) → (M : Trm σ (Γ ∙ τ)) →
  subst (zero* ρ M) (succ ρ) ≡ subst M (succ ρ `∙ zero ρ)
subst-succ ρ M rewrite sub-sub (succ ρ) (ι^Env  `∙ (ren₀-zero ρ)) M =
  subst-ext M [ P ][ succ-ren₀-zero ρ ,,, (λ v → PEq.refl) ]
  where P = λ {τ} v →
          var (succ ρ *-Sub (sub₀-zero ρ)) v ≡ var (succ ρ `∙ zero ρ) {τ} v

-- iterated sequential substitution 'subst₀'

subst₀ : ∀ {Γ} {σ} → (ρ : Env₀ Γ) → (M : Trm σ Γ) → Trm₀ σ
subst₀ {ε} ρ M = M
subst₀ {Γ ∙ τ} ρ M = subst₀ (succ ρ) (zero* ρ M) 

-- parallel substitution 'subst' is iterated sequential substitution 'subst₀'

subst-equiv : ∀ {Γ} {σ} → (ρ : Env₀ Γ) → (M : Trm σ Γ) →
  subst₀ ρ M ≡ subst M ρ
subst-equiv   {ε}   ρ M rewrite ι^Env₀-lemma ρ M = PEq.refl
subst-equiv {Γ ∙ τ} ρ M rewrite subst-equiv (succ ρ) (zero* ρ M) |
                                subst-succ ρ M
    = subst-ext M (cons-rho ρ)

-- iterated βV reduction

data _→βV_ : GRel₀^T where
  →βV-refl : {σ : Ty} {M : Trm₀ σ} → M →βV M
  →βV-step : {σ τ : Ty} {M : Trm₀ τ} {N : (σ ⊢ Trm τ) _} {V : _} →
    M →βV (βV N V) → M →βV (N ⟨ V /var₀⟩)

lemma-2-3i-βV : {τ : Ty} {M N : Trm₀ τ} {V : Val₀ τ} →
                (dev : M ⇓ V) → (red : M →βV N) → N ⇓ V
lemma-2-3i-βV dev →βV-refl = dev
lemma-2-3i-βV dev (→βV-step red) with lemma-2-3i-βV dev red
lemma-2-3i-βV dev (→βV-step red) | ⇓app der = der

lemma-2-3ii-βV : {τ : Ty} {M N : Trm₀ τ} {V : Val₀ τ} →
                 (red : M →βV N) → (dev : N ⇓ V) → M ⇓ V
lemma-2-3ii-βV →βV-refl dev = dev
lemma-2-3ii-βV (→βV-step red) dev = lemma-2-3ii-βV red (⇓app dev)

lemma-2-10i-βV : {ℓ^V : Level} {τ : Ty} {R : GRel^V {ℓ^V} {τ}}
  {M N P : Trm₀ τ} → M →βV P → (M [ R ]^T N) → P [ R ]^T N
lemma-2-10i-βV red r = r ∘ (lemma-2-3ii-βV red)

lemma-2-10ii-βV : {ℓ^V : Level} {τ : Ty} {R : GRel^V {ℓ^V} {τ}}
  {M N P : Trm₀ τ} → (M [ R ]^T N) → N →βV P → M [ R ]^T P
lemma-2-10ii-βV r red der with r der
... | V , derM , rUV = V , lemma-2-3i-βV derM red , rUV

-- Reduction under application (term application simulated with let).
data _→$_ : GRel₀^T where
 →βV-$ : {σ : Ty} {M N : Trm₀ σ} → M →βV N → M →$ N
 →MN-$ : {σ τ : Ty} {M M' : Trm₀ σ} {N : (σ ⊢ Trm τ) _} →
   M →$ M' → `let M N →$ `let M' N

lemma-2-3i-$ : {τ : Ty} {M N : Trm₀ τ} {V : Val₀ τ} →
                (dev : M ⇓ V) → (red : M →$ N) → N ⇓ V
lemma-2-3i-$ dev (→βV-$ βV) = lemma-2-3i-βV dev βV
lemma-2-3i-$ (⇓let derM derN) (→MN-$ red) with lemma-2-3i-$ derM red
... | iH = ⇓let iH derN

lemma-2-3ii-$ : {τ : Ty} {M N : Trm₀ τ} {V : Val₀ τ} →
                 (red : M →$ N) → (dev : N ⇓ V) → M ⇓ V
lemma-2-3ii-$ (→βV-$ βV) dev = lemma-2-3ii-βV βV dev
lemma-2-3ii-$ (→MN-$ red) (⇓let derM derN) =
  ⇓let (lemma-2-3ii-$ red derM) derN

lemma-2-10i-$ : {ℓ^V : Level} {τ : Ty} {R : GRel^V {ℓ^V} {τ}}
  {M N P : Trm₀ τ} → M →$ P → (M [ R ]^T N) → P [ R ]^T N
lemma-2-10i-$ red r = r ∘ (lemma-2-3ii-$ red)

lemma-2-10ii-$ : {ℓ^V : Level} {τ : Ty} {R : GRel^V {ℓ^V} {τ}}
  {M N P : Trm₀ τ} → (M [ R ]^T N) → N →$ P → M [ R ]^T P
lemma-2-10ii-$ r red der with r der
... | V , derM , rUV = V , lemma-2-3i-$ derM red , rUV

-- iterated βV redex construction

βVΓ : ∀ {Γ} {σ} → (ρ : Env₀ Γ) → (M : Trm σ Γ) → Trm₀ σ
βVΓ   {ε}   ρ M = M
βVΓ {Γ ∙ τ} ρ M = βVΓ (succ ρ) (βV M (ren₀-zero ρ))

βV-subst₀ : ∀ {Γ} {σ} → (ρ : Env₀ Γ) → (M : Trm σ Γ) → βVΓ ρ M →βV subst M ρ
βV-subst₀   {ε}   ρ M rewrite ι^Env₀-lemma ρ M = →βV-refl
βV-subst₀ {Γ ∙ τ} ρ M with βV-subst₀ (succ ρ) (βV M (ren₀-zero ρ))
... | ih rewrite PEq.sym (subst-equiv ρ M) | succ-ren₀-zero ρ |
                 subst-equiv (succ ρ) (zero* ρ M) |
                 subst-succ ρ M
         with →βV-step ih
... | prf rewrite PEq.sym (lemma34 M (succ ρ) (zero ρ)) = prf

-- VCC contexts; no additional renaming/substitution in holes

infixr 20 VCC⟪_⊢_⟫

data VCC⟪_⊢_⟫ (Γ : Cx) (τ : Ty) : {f : CBV} → PreModel L.zero

 where

  `λ   : admits-λ λ {f} → VCC⟪ Γ ⊢ τ ⟫ {f}

  `exp : ∀ {f} {σ} → [ Exp {f} σ ⟶ VCC⟪ Γ ⊢ τ ⟫ {f} σ ]
    -- no holes; saves re-traversal

  ⟪-⟫  : VCC⟪ Γ ⊢ τ ⟫ {`trm} τ Γ -- hole

  `val : {σ : Ty} → [ VCC⟪ Γ ⊢ τ ⟫ {`val} σ  ⟶  VCC⟪ Γ ⊢ τ ⟫ {`trm} σ ]
    -- lifting

  _`$_ : admits-$   λ {f} → VCC⟪ Γ ⊢ τ ⟫ {f}
  `if  : admits-if  λ {f} → VCC⟪ Γ ⊢ τ ⟫ {f}
  `let : admits-let λ {f} → VCC⟪ Γ ⊢ τ ⟫ {f}

-- instantiation

_⟪_⟫VCC : ∀ {f} {Γ Δ} {σ τ}
       (P : VCC⟪ Γ ⊢ σ ⟫ {f} τ Δ) (T : Trm σ Γ) → Exp {f} τ Δ

`exp E ⟪ T ⟫VCC =  E
`λ M   ⟪ T ⟫VCC = `λ (M ⟪ T ⟫VCC)

⟪-⟫    ⟪ T ⟫VCC = T

(`val V)  ⟪ T ⟫VCC = `val (V ⟪ T ⟫VCC)

(V `$ W)  ⟪ T ⟫VCC = (V ⟪ T ⟫VCC) `$ (W ⟪ T ⟫VCC)
`if B L R ⟪ T ⟫VCC = `if  (B ⟪ T ⟫VCC) (L ⟪ T ⟫VCC) (R ⟪ T ⟫VCC)
`let M N  ⟪ T ⟫VCC = `let (M ⟪ T ⟫VCC) (N ⟪ T ⟫VCC)

-- action of substitution by iterated βV redex construction 

VCC-sub : ∀ {Γ Δ} {σ τ} → Env₀ Δ → VCC⟪ Γ ⊢ σ ⟫ {`trm} τ Δ →
  VCC⟪ Γ ⊢ σ ⟫ {`trm} τ ε
VCC-sub {Δ = ε} ρ C = C
VCC-sub {Δ = Δ ∙ ω} ρ C =
  VCC-sub (succ ρ) (`λ C `$ (`exp (ren₀-zero ρ))) 

-- commutes with instantiation 

VCC-sub-βV : ∀ {Γ Δ} {σ τ} →
  (ρ : Env₀ Δ) → (C : VCC⟪ Γ ⊢ σ ⟫ τ Δ) → (M : Trm σ Γ) → 
  (VCC-sub ρ C) ⟪ M ⟫VCC ≡ βVΓ ρ (C ⟪ M ⟫VCC)
VCC-sub-βV {Δ = ε}     ρ C M = PEq.refl
VCC-sub-βV {Δ = Δ ∙ τ} ρ C =
  VCC-sub-βV (succ ρ) ((`λ C) `$ (`exp (ren₀-zero ρ))) 

-- composition of contexts

_⟪∘⟫VCC_ : ∀ {f} {Γ Δ Ξ} {σ τ υ}
          (P : VCC⟪ Δ ⊢ σ ⟫ {f} τ Ξ)
          (Q : VCC⟪ Γ ⊢ υ ⟫ {`trm} σ Δ) → VCC⟪ Γ ⊢ υ ⟫ {f} τ Ξ
`exp E     ⟪∘⟫VCC Q = `exp E
`λ M       ⟪∘⟫VCC Q = `λ (M ⟪∘⟫VCC Q)
⟪-⟫        ⟪∘⟫VCC Q =  Q
`val P     ⟪∘⟫VCC Q = `val (P ⟪∘⟫VCC Q)
(F `$ A)   ⟪∘⟫VCC Q = F ⟪∘⟫VCC Q `$ A ⟪∘⟫VCC Q
`if B L R  ⟪∘⟫VCC Q = `if (B ⟪∘⟫VCC Q) (L ⟪∘⟫VCC Q) (R ⟪∘⟫VCC Q)
`let P R   ⟪∘⟫VCC Q = `let (P ⟪∘⟫VCC Q) (R ⟪∘⟫VCC Q)

-- commutation between composition and instantiation

_⟪∘_⟫VCC_ : ∀ {f} {Γ Δ Ξ} {σ τ υ} (P : VCC⟪ Δ ⊢ σ ⟫ {f} τ Ξ) (T : Trm υ Γ) →
       (Q : VCC⟪ Γ ⊢ υ ⟫ {`trm} σ Δ) →
       (P ⟪∘⟫VCC Q) ⟪ T ⟫VCC ≡ P ⟪ Q ⟪ T ⟫VCC ⟫VCC

`exp E    ⟪∘ T ⟫VCC Q = PEq.refl
`λ M      ⟪∘ T ⟫VCC Q rewrite M ⟪∘ T ⟫VCC Q = PEq.refl

⟪-⟫       ⟪∘ T ⟫VCC Q = PEq.refl
`val P    ⟪∘ T ⟫VCC Q rewrite P ⟪∘ T ⟫VCC Q = PEq.refl
(F `$ A)  ⟪∘ T ⟫VCC Q rewrite F ⟪∘ T ⟫VCC Q | A ⟪∘ T ⟫VCC Q = PEq.refl
`if B L R ⟪∘ T ⟫VCC Q
  rewrite B ⟪∘ T ⟫VCC Q | L ⟪∘ T ⟫VCC Q | R ⟪∘ T ⟫VCC Q = PEq.refl
`let P R  ⟪∘ T ⟫VCC Q rewrite P ⟪∘ T ⟫VCC Q | R ⟪∘ T ⟫VCC Q = PEq.refl

-- K-approximation wrt K = VCC

vcc-apx : ∀ {f} {Γ} {υ} → Rel^E {f} {L.zero} {Γ} {υ}
vcc-apx {f} = case f return (λ f → ∀ {Γ} {υ} → Rel^E {f} {_} {Γ} {υ})
 of λ { `val → apxV ; `trm → apxT }
 where
  apxV : ∀ {Γ} {τ} → Rel^V {_} {Γ} {τ}
  apxT : ∀ {Γ} {τ} → Rel^T {_} {Γ} {τ}
  apxV {Γ} {τ}     = _[ apxT {Γ} {τ} ]^V_
  apxT {Γ} {τ} M N =
    {υ : Ty} (P : VCC⟪ Γ ⊢ τ ⟫ υ ε) →
    gnd-eqv₀ {`trm} (P ⟪ M ⟫VCC) (P ⟪ N ⟫VCC)

-- open ground equivalence follows trivially: use the obvious context, 
-- the substitution instance of the hole itself!

vcc-apx→gnd-eqv^T : ∀ {Γ} {τ} {M N} → vcc-apx M N → gnd-eqv {`trm} {Γ} {τ} M N
vcc-apx→gnd-eqv^T {Γ} {τ} {M} {N} sMN ρ = gnd-eqv-subst
  where P : VCC⟪ Γ ⊢ τ ⟫ τ ε
        P = VCC-sub ρ ⟪-⟫ 

        βV-subst : ∀ M → (P ⟪ M ⟫VCC) →βV subst M ρ
        βV-subst M rewrite VCC-sub-βV ρ ⟪-⟫ M with βV-subst₀ ρ M 
        ... | prf rewrite subst-equiv ρ M = prf 

        gnd-eqv-subst : gnd-eqv₀ {`trm} (subst M ρ) (subst N ρ)
        gnd-eqv-subst = lemma-2-10i-βV (βV-subst M)
                                   (lemma-2-10ii-βV (sMN P) (βV-subst N))

vcc-apx₀ : GRel₀^E
vcc-apx₀ {f} = case f return (λ f → ∀ {υ} → Rel^E {f} {_} {ε} {υ})
 of λ { `val → apxV ; `trm → apxT }
 where
  apxV : GRel₀^V
  apxT : GRel₀^T
  apxV {τ} = _[ apxT {τ} ]^V_
  apxT     = vcc-apx {`trm} {ε}

-- Convert an VCC to a VSC: the star in the paper

vcc-to-vsc : ∀ {f} {Γ Δ} {σ τ} → VCC⟪ Γ ⊢ σ ⟫ {f} τ Δ → VSC⟪ Γ ⊢ σ ⟫ {f} τ Δ
vcc-to-vsc (`λ M) = `λ (vcc-to-vsc M)
vcc-to-vsc (`exp E) = `exp E
vcc-to-vsc ⟪-⟫ = ⟪- ι^Env -⟫
vcc-to-vsc (`val P) = `val (vcc-to-vsc P)
vcc-to-vsc (F `$ A) = (vcc-to-vsc F) `$ (vcc-to-vsc A)
vcc-to-vsc (`if B L R) = `if (vcc-to-vsc B) (vcc-to-vsc L) (vcc-to-vsc R)
vcc-to-vsc (`let P Q) = `let (vcc-to-vsc P) (vcc-to-vsc Q)

vcc→vsc⟪_⟫ : ∀ {f} {Γ Δ} {σ τ} →
  (M : Trm σ Γ) → (P : VCC⟪ Γ ⊢ σ ⟫ {f} τ Δ) →
  (vcc-to-vsc P) ⟪ M ⟫ ≡ P ⟪ M ⟫VCC
vcc→vsc⟪ M ⟫ (`λ P) rewrite vcc→vsc⟪ M ⟫ P = PEq.refl
vcc→vsc⟪ M ⟫ (`exp E) = PEq.refl
vcc→vsc⟪ M ⟫ ⟪-⟫ = ι^Env-lemma M
vcc→vsc⟪ M ⟫ (`val P) rewrite vcc→vsc⟪ M ⟫ P = PEq.refl
vcc→vsc⟪ M ⟫ (F `$ A) rewrite vcc→vsc⟪ M ⟫ F | vcc→vsc⟪ M ⟫ A = PEq.refl
vcc→vsc⟪ M ⟫ (`if B L R)
  rewrite vcc→vsc⟪ M ⟫ B | vcc→vsc⟪ M ⟫ L | vcc→vsc⟪ M ⟫ R = PEq.refl
vcc→vsc⟪ M ⟫ (`let P Q) rewrite vcc→vsc⟪ M ⟫ P | vcc→vsc⟪ M ⟫ Q = PEq.refl

-- VCCs are contained within VSCs

vsc-apx→vcc-apx^T :
  ∀ {Γ} {τ} {M N} → vsc-apx M N → vcc-apx {`trm} {Γ} {τ} M N
vsc-apx→vcc-apx^T {Γ} {τ} {M} {N} sMN P with sMN (vcc-to-vsc P)
... | hyp rewrite vcc→vsc⟪ M ⟫ P | vcc→vsc⟪ N ⟫ P = hyp

vsc-apx₀→vcc-apx₀^T : ∀ {τ} {M N : Trm₀ τ} → vsc-apx₀ M N → vcc-apx₀ M N
vsc-apx₀→vcc-apx₀^T = vsc-apx→vcc-apx^T {ε}
