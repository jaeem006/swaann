module Equivalence where

open import Data.Vec
open import Function
open import Data.Product
open import Data.Maybe

open import Decidable
open import Grammar
open import BigStep
open import SmallStep

-- Eqv : ∀ {n} {s : Stm n} {σ σ₁} → ⟨ s , σ ⟩⇒ σ₁ ⇔  ⟨ s , σ ⟩↦* σ₁
-- Eqv {n} = Data.Prouct._,_ to  from ∘ proj₂
--  where
to : ∀ {n}{s : Stm n}{σ σ₁ : State n} → ⟨ s , σ ⟩⇒ σ₁ → ⟨ s , σ ⟩↦* σ₁
to assB =  0 , {!  !}
to skipB = {!!}
to (compB s₁ s₂) = {!!}
to (if-TB x x₁) = {!!}
to (if-FB x x₁) = {!!}
to (while-TB x x₁ x₂) = {!!}
to (while-FB x) = {!!}

mutual
  prepend : ∀ {n} {σ σ₁ σ₂} {s₁ s₂ : Stm n} →
            ⟨ s₁ , σ ⟩↦⟨ s₂ , σ₁ ⟩ →
            -- se hace en un sólo paso para garantizar la recursión estructural de los naturales
            ⟨ s₂ , σ₁ ⟩⇒ σ₂ →
            ⟨ s₁ , σ ⟩⇒ σ₂
  prepend = {!!}

  from : ∀ {n}{s : Stm n}{σ σ₁ : State n}{k} → ⟨ s , σ ⟩ k ↦ σ₁ → ⟨ s , σ ⟩⇒ σ₁
  from x = {!!}
