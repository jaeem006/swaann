module Equivalence where

open import Data.Vec
open import Function
open import Data.Product
open import Data.Maybe

open import Decidable
open import Grammar
open import BigStep
open import SmallStep

BtoS : ∀ {n}{s : Stm n}{σ σ₁ : State n} → ⟨ s , σ ⟩⇒ σ₁ → ⟨ s , σ ⟩↦* σ₁
BtoS assB =  {!!}
BtoS skipB = {!!}
BtoS (compB s₁ s₂) = {!!}
BtoS (if-TB x x₁) = {!!}
BtoS (if-FB x x₁) = {!!}
BtoS (while-TB x x₁ x₂) = {!!}
BtoS (while-FB x) = {!!}
