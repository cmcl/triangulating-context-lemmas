{---------------------------------------------------------------}
{-- Basic prelude for the development.                        --}
{-- Removing dependency on Data.* imports which maybe causing --}
{-- GHC compilation issues with older compiler versions.      --}
{---------------------------------------------------------------}
module tri-prelude where

open import Level as L using (Level ; _⊔_)
open import Function as F

-- Mifix operator precedence
infix 0 if_then_else_
infixr 2 _×_ _,_

-- Interpretation of base types in our calculus

data Unit : Set where
  ⟨⟩ : Unit

data Bool : Set where
  tt ff : Bool

data Nat : Set where
  ℤ   : Nat
  suc : Nat → Nat

-- From base library
if_then_else_ : ∀ {a} {A : Set a} → Bool → A → A → A
if tt then t else f = t
if ff then t else f = f

-- Dependent sum types
record Sg {s t} (S : Set s) (T : S → Set t) : Set (s ⊔ t) where
  constructor _,_
  field
    fst : S
    snd : T fst

_×_ : ∀ {s t} → (S : Set s) → (T : Set t) → Set (s ⊔ t)
S × T = Sg S (λ _ → T)

∃ : ∀ {s t} {S : Set s} → (T : S → Set t) → Set (s ⊔ t)
∃ {S = S} T = Sg S T

uncurry : ∀ {s t u} {S : Set s} {T : S → Set t} {U : Sg S T → Set u} →
            (f : (x : S) → (y : T x) → U (x , y)) →
            (p : Sg S T) → U p
uncurry f (x , y) = f x y

-- Properites using propositional equality

module PEq {a} {A : Set a} where
  open import Agda.Builtin.Equality public

  cong : ∀ {b} {B : Set b} (f : A → B) {x y} → x ≡ y → f x ≡ f y
  cong f refl = refl

  cong₂ : ∀ {b c} {B : Set b} {C : Set c} (f : A → B → C) {x y u v} →
          x ≡ y → u ≡ v → f x u ≡ f y v
  cong₂ f refl refl = refl

  sym : ∀ {x y : A} → x ≡ y → y ≡ x
  sym refl = refl

  trans : ∀ {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans refl refl = refl

open PEq using (_≡_) public
