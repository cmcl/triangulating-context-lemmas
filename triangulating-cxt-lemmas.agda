module triangulating-cxt-lemmas where

{-- Some things to note:

   * The formalisation uses the term "simulation" whereas the paper uses the
     term "approximation" when referring the relations. Additionally,
     observational approximation is called "cxt-sim" here.

-}

-- Import the calculus
open import lambda-fg
-- ACCM defines the generic evaluations and substitution traversals
open import acmm
open import relations
open import big-step-prop
open import obs-apx
open import tri-big-step
open import frm-stk-prop
open import tri-frm-stk
