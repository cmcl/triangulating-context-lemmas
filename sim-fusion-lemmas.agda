{-- Using the generic Allais et al. machinery to prove simulation and fusion
 -- results. -}
module sim-fusion-lemmas where

open import Level as L using (Level ; _⊔_)
open import Function as F hiding (_∋_ ; _$_)

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

-- Syntactic fusion result
syntacticFusion : {ℓ^A ℓ^B ℓ^C ℓ^RVBC ℓ^RV : Level}
 {𝓥^A : PreModel ℓ^A} {Θ^A : Model 𝓥^A} {mod^A : Model₀ Θ^A}
 {𝓥^B : PreModel ℓ^B} {Θ^B : Model 𝓥^B} {mod^B : Model₀ Θ^B}
 {𝓥^C : PreModel ℓ^C} {Θ^C : Model 𝓥^C} {mod^C : Model₀ Θ^C}
 {var^A : Morphism Θ^A Val}
 {var^B : Morphism Θ^B Val}
 {var^C : Morphism Θ^C Val}
 {𝓥^R-BC : RPreModel 𝓥^B 𝓥^C ℓ^RVBC}
 {𝓥^R : {Γ Δ Θ : Cx} →
         (Γ -Env) 𝓥^A Δ → (Δ -Env) 𝓥^B Θ → (Γ -Env) 𝓥^C Θ → Set (ℓ^RV)} →
 SyntacticFusion mod^A mod^B mod^C var^A var^B var^C 𝓥^R-BC 𝓥^R →
 Fusion {var^A = var^A} {var^B = var^B} {var^C = var^C}
        (syntactic mod^A) (syntactic mod^B) (syntactic mod^C)
        𝓥^R-BC 𝓥^R PropEq
syntacticFusion synF = record
  {
  reifyₐ = id
  ;
  𝓥^R∙ = 𝓥^R∙
  ;
  𝓥^Rth = 𝓥^Rth
  ;
  R⟦b⟧ = λ b _ → PEq.refl {x = `b b}
  ;
  R⟦var⟧ = R⟦var⟧
  ;
  R⟦λ⟧ = λ L _ → PEq.cong λλ (L weak var₀-BC)
  ;
  R⟦val⟧ = λ V _ → PEq.cong Val→Trm V
  ;
  R⟦$⟧ = λ F A _ → PEq.cong₂ _`$_ F A
  ;
  R⟦if⟧ = λ B L R _ → PEq.cong₂ (uncurry `if) (PEq.cong₂ _,_ B L) R
  ;
  R⟦let⟧ = λ M N _ → PEq.cong₂ `let M (N weak var₀-BC)
  } where open SyntacticFusion synF

ren-ren-R∙ : ∀ {Γ Δ Θ} {σ} →
  {ρ^A : Γ ⊆ Δ} → {ρ^B : Δ ⊆ Θ} → {ρ^C : Γ ⊆ Θ} → {u^B u^C : Var σ Θ} →
  (ρ^R : ∀ {τ} v → var ρ^B {τ} (var ρ^A v) ≡ var ρ^C v) →
  (u^R : u^B ≡ u^C) →
  ∀ {τ} v → var (ρ^B `∙ u^B) {τ} (var (ext₀^Var ρ^A) v) ≡ var (ρ^C `∙ u^C) v
ren-ren-R∙ {Γ} {Δ} {Θ} {σ} {ρ^A} {ρ^B} {ρ^C} {u^B} {u^C} ρ^R eq =
  [ P ][ eq ,,, ρ^R ]
  where P = λ {τ} v →
              var (ρ^B `∙ u^B) {τ} (var (ext₀^Var ρ^A) v) ≡ var (ρ^C `∙ u^C) v

-- Ren-ren
Ren-ren-fusion :
  SyntacticFusion 𝓥ar₀ 𝓥ar₀ 𝓥ar₀ Var→Val Var→Val Var→Val
                  PropEq
                  (λ ρ^A ρ^B ρ^C →
                     ∀ {τ} v → var ρ^B (var ρ^A {τ} v) ≡ var ρ^C v)
Ren-ren-fusion = record
  {
  𝓥^R∙ = ren-ren-R∙
  ;
  𝓥^Rth = λ inc ρ^R v → PEq.cong (var inc) (ρ^R v)
  ;
  R⟦var⟧ = λ v ρ^R → PEq.cong `var (ρ^R v)
  ;
  var₀-BC = PEq.refl
  }

ren-sub-R∙ : ∀ {Γ Δ Θ} {σ} →
  {r : Γ ⊆ Δ} → {ρ^B : Δ ⊨ Θ} → {ρ^C : Γ ⊨ Θ} → {u^B u^C : Val σ Θ} →
  (ρ^R : ∀ {τ} v → var ρ^B {τ} (var r v) ≡ var ρ^C v) →
  (u^R : u^B ≡ u^C) →
  ∀ {τ} v → var (ρ^B `∙ u^B) {τ} (var (ext₀^Var r) v) ≡ var (ρ^C `∙ u^C) v
ren-sub-R∙ {Γ} {Δ} {Θ} {σ} {r} {ρ^B} {ρ^C} {u^B} {u^C} ρ^R eq =
  [ P ][ eq ,,, ρ^R ]
  where P = λ {τ} v →
              var (ρ^B `∙ u^B) {τ} (var (ext₀^Var r) v) ≡ var (ρ^C `∙ u^C) v

-- Ren-Sub fusion
Ren-sub-fusion :
  SyntacticFusion 𝓥ar₀ 𝓥al₀ 𝓥al₀ Var→Val Val→Val Val→Val
                  PropEq
                  (λ ρ^A ρ^B ρ^C →
                     ∀ {τ} v → var ρ^B (var ρ^A {τ} v) ≡ var ρ^C v)
Ren-sub-fusion = record
  {
  𝓥^R∙ = ren-sub-R∙
  ;
  𝓥^Rth = λ inc ρ^R v → PEq.cong (inc *-Var_) (ρ^R v)
  ;
  R⟦var⟧ = λ v ρ^R → ρ^R v
  ;
  var₀-BC = PEq.refl
  }

-- Applying a substitution then a renaming is the same as applying a
-- substitution.
sub-ren-R∙ : ∀ {Γ Δ Θ} {σ} →
  {ρ^A : Γ ⊨ Δ} → {ρ^B : Δ ⊆ Θ} → {ρ^C : Γ ⊨ Θ} →
  {u^B : Var σ Θ} {u^C : Val σ Θ} →
  (ρ^R : ∀ {τ} v → ren (var ρ^A {τ} v) ρ^B ≡ var ρ^C v) →
  (u^R : rmodel VarVal^R u^B u^C) →
  ∀ {τ} v → ren (var (ext₀^Env ρ^A) {τ} v) (ρ^B `∙ u^B) ≡ var (ρ^C `∙ u^C) v
sub-ren-R∙ {Γ} {Δ} {Θ} {σ} {ρ^A} {ρ^B} {ρ^C} {u^B} {u^C} ρ^R eq =
  let module RenRen = Fuse (syntacticFusion Ren-ren-fusion) in
  [ P ][ eq ,,, (λ v →
                   PEq.trans (RenRen.lemma (var ρ^A v) {ρ^A = weak}
                                          {ρ^B = ρ^B `∙ u^B} (λ v → PEq.refl))
                                          (ρ^R v)) ]
  where P = λ {τ} v →
              ren (var (ext₀^Env ρ^A) {τ} v) (ρ^B `∙ u^B) ≡ var (ρ^C `∙ u^C) v

-- Sub-ren fusion
Sub-ren-fusion :
  SyntacticFusion 𝓥al₀ 𝓥ar₀ 𝓥al₀ Val→Val Var→Val Val→Val
                  VarVal^R
                  (λ ρ^A ρ^B ρ^C →
                     ∀ {τ} v → ren (var ρ^A {τ} v) ρ^B ≡ var ρ^C v)
Sub-ren-fusion =
  let module RenRen = Fuse (syntacticFusion Ren-ren-fusion) in
  record
  {
  𝓥^R∙ = λ {Γ} {Δ} {Θ} {σ} {ρ^A} {ρ^B} {ρ^C} ρ^R u^R →
           sub-ren-R∙ {ρ^A = ρ^A} {ρ^B} {ρ^C} ρ^R u^R
  ;
  𝓥^Rth = λ {Γ} {Δ} {Θ} {ρ^A} {ρ^B} {ρ^C} inc ρ^R v →
            PEq.trans (PEq.sym (RenRen.lemma (var ρ^A v) {ρ^A = ρ^B}
                                             {ρ^B = inc} (λ v → PEq.refl)))
                      (PEq.cong (inc *-Var_) (ρ^R v))
  ;
  R⟦var⟧ = λ v ρ^R → ρ^R v
  ;
  var₀-BC = PEq.refl
  }

sub-sub-R∙ : ∀ {Γ Δ Θ} {σ} →
  {ρ^A : Γ ⊨ Δ} → {ρ^B : Δ ⊨ Θ} → {ρ^C : Γ ⊨ Θ} →
  {u^B u^C : Val σ Θ} →
  (ρ^R : ∀ {τ} v → subst (var ρ^A {τ} v) ρ^B ≡ var ρ^C v) →
  (u^R : u^B ≡ u^C) →
  ∀ {τ} v → subst (var (ext₀^Env ρ^A) {τ} v) (ρ^B `∙ u^B) ≡ var (ρ^C `∙ u^C) v
sub-sub-R∙ {Γ} {Δ} {Θ} {σ} {ρ^A} {ρ^B} {ρ^C} {u^B} {u^C} ρ^R eq =
  let module RenSub = Fuse (syntacticFusion Ren-sub-fusion) in
  [ P ][ eq ,,, (λ v →
                   PEq.trans (RenSub.lemma (var ρ^A v) {ρ^A = weak}
                                          {ρ^B = ρ^B `∙ u^B} (λ v → PEq.refl))
                                          (ρ^R v)) ]
  where P = λ {τ} v →
            subst (var (ext₀^Env ρ^A) {τ} v) (ρ^B `∙ u^B) ≡ var (ρ^C `∙ u^C) v

Sub-sub-fusion :
  SyntacticFusion 𝓥al₀ 𝓥al₀ 𝓥al₀ Val→Val Val→Val Val→Val PropEq
                  (λ ρ^A ρ^B ρ^C →
                     ∀ {τ} v → subst (var ρ^A {τ} v) ρ^B ≡ var ρ^C v)
Sub-sub-fusion =
  let module SubRen = Fuse (syntacticFusion Sub-ren-fusion) in
  record
  {
  𝓥^R∙ = λ {Γ} {Δ} {Θ} {σ} {ρ^A} {ρ^B} {ρ^C} ρ^R u^R →
           sub-sub-R∙ {ρ^A = ρ^A} {ρ^B} {ρ^C} ρ^R u^R
  ;
  𝓥^Rth = λ {Γ} {Δ} {Θ} {ρ^A} {ρ^B} {ρ^C} inc ρ^R v →
            PEq.trans (PEq.sym (SubRen.lemma (var ρ^A v) {ρ^A = ρ^B}
                                             {ρ^B = inc} (λ v → PEq.refl)))
                      (PEq.cong (inc *-Var_) (ρ^R v))
  ;
  R⟦var⟧ = λ v ρ^R → ρ^R v
  ;
  var₀-BC = PEq.refl
  }

sub-sub : ∀ {f} {Γ Δ Ξ} {σ} → (ρ : Δ ⊨ Ξ) → (ρ' : Γ ⊨ Δ) → (E : Exp {f} σ Γ) →
 (ρ *-Val (ρ' *-Val E)) ≡ ((ρ *-Sub ρ') *-Val E)
sub-sub ρ ρ' E = lemma E {ρ^A = ρ'} {ρ^B = ρ} (λ v → PEq.refl)
  where open Fuse (syntacticFusion Sub-sub-fusion)

lemma33 : ∀ {f} {Γ Δ Ξ} {σ} → (ρ : Δ ⊨ Ξ) → (ρ' : Γ ⊨ Δ) → (E : Exp {f} σ Γ) →
 ((ρ *-Sub ρ') *-Val E) ≡ (ρ *-Val (ρ' *-Val E))
lemma33 ρ ρ' E = PEq.sym (sub-sub ρ ρ' E)

lemma33-ren : ∀ {f} {Γ Δ Ξ} {σ} → (r : Δ ⊆ Ξ) → (r' : Γ ⊆ Δ) →
  (E : Exp {f} σ Γ) → (trans^Var r' r *-Var E) ≡ (r *-Var (r' *-Var E))
lemma33-ren r r' E = PEq.sym (lemma E {ρ^A = r'} {ρ^B = r} (λ v → PEq.refl))
  where open Fuse (syntacticFusion Ren-ren-fusion)

ext₀^Var-ext : ∀ {Γ Δ} {σ} → {r r' : Γ ⊆ Δ} →
                 (∀ {τ} v → var r {τ} v ≡ var r' v) →
 ∀ {τ} v → var (ext₀^Var {σ} {Γ} r) {τ} v ≡ var (ext₀^Var r') v
ext₀^Var-ext {Γ} {Δ} {σ} {r} {r'} eq =
  [ P ][ PEq.refl ,,,  PEq.cong su ∘ eq ]
 where P = λ {τ} v → var (ext₀^Var {σ} {Γ} r) {τ} v ≡ var (ext₀^Var r') v

ren-sub : ∀ {f} {Γ Δ Θ} {σ} → (E : Exp {f} σ Γ) →
  (r : Γ ⊆ Δ) → (ρ : Δ ⊨ Θ) → {ρ' : Γ ⊨ Θ} →
  (∀ {τ} v → var ρ {τ} (var r v) ≡ var ρ' v) →
  subst (r *-Var E) ρ ≡ subst E ρ'
ren-sub E r ρ {ρ'} eq = lemma E {r} {ρ} eq
  where open Fuse (syntacticFusion Ren-sub-fusion)

-- Special cases of ren-sub

-- The substitution and renaming compose to the identity substitution.
ι^Var^Env-lemma-aux :
  ∀ {f} {Γ Δ} {σ} → (E : Exp {f} σ Γ) → (r : Γ ⊆ Δ) → (ρ : Δ ⊨ Γ) →
  (∀ {τ} v → var ρ {τ} (var r v) ≡ `var v) →
  subst (r *-Var E) ρ ≡ E
ι^Var^Env-lemma-aux E r ρ eq with ren-sub E r ρ eq
... | prf rewrite ι^Env-lemma-aux (λ v → PEq.refl) E = prf

-- Special case of ι^Var^Env: weakening and a single substition.
weak-sub : ∀ {f} {Γ} {σ τ} → (V : Val τ Γ) → (E : Exp {f} σ Γ) →
  (weak *-Var E) ⟨ V /var₀⟩ ≡ E
weak-sub V E = ι^Var^Env-lemma-aux E weak (ι^Env `∙ V) (λ v → PEq.refl)

lemma34 : ∀ {f} {Γ Δ} {σ τ} → (E : (σ ⊢ Exp {f} τ) Γ) → (ρ : Γ ⊨ Δ) → ∀ U →
 subst E (ρ `∙ U) ≡ subst E (ext₀^Env ρ) ⟨ U /var₀⟩
lemma34 {f} {Γ} {Δ} E ρ U rewrite sub-sub (ι^Env {Δ} `∙ U) (ext₀^Env ρ) E =
  subst-ext E [ P ][ PEq.refl ,,, (λ v → PEq.sym (weak-sub U (var ρ v))) ]
  where
    P = λ {τ} v → var (ρ `∙ U) {τ} v ≡ var ((ι^Env `∙ U) *-Sub (ext₀^Env ρ)) v

sub-ren : ∀ {f} {Γ Δ Θ} {σ} → (E : Exp {f} σ Γ) →
  (ρ : Γ ⊨ Δ) → (r : Δ ⊆ Θ) → {ρ' : Γ ⊨ Θ} →
  (∀ {τ} v → ren (var ρ {τ} v) r ≡ var ρ' v) →
  ren (subst E ρ) r ≡ subst E ρ'
sub-ren E ρ r {ρ'} eq = lemma E {ρ} {r} eq
  where open Fuse (syntacticFusion Sub-ren-fusion)

ren-sub→sub-ren : ∀ {f} {Γ Δ Ξ Ω} {σ} →
  (E : Exp {f} σ Γ) → (r : Γ ⊆ Δ) → (r' : Ω ⊆ Ξ)
  (ρ : Δ ⊨ Ξ) → (ρ' : Γ ⊨ Ω) →
  (∀ {τ} v → var ρ {τ} (var r v) ≡ ren (var ρ' v) r') →
  subst (ren E r) ρ ≡ ren (subst E ρ') r'
ren-sub→sub-ren E r r' ρ ρ' eq =  PEq.trans prf prf'
  where prf : subst (ren E r) ρ ≡ subst E (Thin.th 𝓥al ρ' r')
        prf = ren-sub E r ρ eq

        prf' : subst E (Thin.th 𝓥al ρ' r') ≡ ren (subst E ρ') r'
        prf' = PEq.sym (sub-ren E ρ' r' (λ v → PEq.refl))
