module SmallStep where

import Data.Bool as Bool using (not)
open import Data.Bool hiding (not; if_then_else_)
open import Data.Empty
open import Data.Fin using (Fin; suc; zero; #_)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Vec
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Unit hiding (_≤?_)
open import Data.Product
open import Data.Maybe
import Level as L

open import Grammar
open import Decidable
open import NatLemmas

infixr 5 _∷_
mutual
--Mutual es importante para avisarle a Agda que habra recursión mutua

 -- Derivaciones con un número especifico de pasos
 ⟨_,_⟩_↦_ : ∀ {n} → Stm n → State n → ℕ → State n → Set
 ⟨_,_⟩_↦_ s σ n σ₁ = ⟨ s , σ ⟩ n ↦[ nothing , σ₁ ]

 ⟨_,_⟩_↦⟨_,_⟩ : ∀ {n} → Stm n → State n → ℕ → Stm n → State n → Set
 ⟨_,_⟩_↦⟨_,_⟩ s₁ σ n s₂ σ₁ = ⟨ s₁ , σ ⟩ n ↦[ just s₂ , σ₁ ]

 -- Derivaciones con un número arbitrarío de pasos
 ⟨_,_⟩↦*_ : ∀ {n} → Stm n → State n → State n → Set
 ⟨_,_⟩↦*_ s σ σ₁ = ∃ λ n → ⟨ s , σ ⟩ n ↦[ nothing , σ₁ ]

 ⟨_,_⟩↦*⟨_,_⟩ : ∀ {n} → Stm n → State n → Stm n → State n → Set
 ⟨_,_⟩↦*⟨_,_⟩ s₁ σ s₂ σ₁ = ∃ λ n → ⟨ s₁ , σ ⟩ n ↦[ just s₂ , σ₁ ]

 -- Un paso de derivación
 ⟨_,_⟩↦_ : ∀ {n} → Stm n → State n → State n → Set
 ⟨_,_⟩↦_ s σ σ₁ = ⟨ s , σ ⟩↦[ nothing , σ₁ ]

 ⟨_,_⟩↦⟨_,_⟩ : ∀ {n} → Stm n → State n → Stm n → State n → Set
 ⟨_,_⟩↦⟨_,_⟩ s₁ σ s₂ σ₁ = ⟨ s₁ , σ ⟩↦[ just s₂ , σ₁ ]

 -- definimos las relgas de semántica operacional de paso pequeño
 data ⟨_,_⟩↦[_,_] {n : ℕ} : Stm n → State n → Maybe (Stm n) → State n → Set where
   assS : ∀ {x a σ} → ⟨ x := a , σ ⟩↦ (σ [ x ]≔ ⟦ a ⟧ᵉ σ)
   skipS : ∀ {σ} → ⟨ skip , σ ⟩↦ σ
   compS1 : ∀ {s₁ s₂ s₁' σ σ₁} → ⟨ s₁ , σ ⟩↦⟨ s₁' , σ₁ ⟩ →
             ⟨ (s₁ , s₂) , σ ⟩↦⟨ (s₁ , s₂) , σ₁ ⟩
   compS2 : ∀ {s₁ s₂ σ σ₁} → ⟨ s₁ , σ ⟩↦ σ₁ → ⟨ (s₁ , s₂) , σ ⟩↦⟨ s₂ , σ₁ ⟩
   if-TS : ∀ {s₁ s₂ σ b} → T (⟦ b ⟧ᵉ σ) → ⟨ if b then s₁ else s₂ , σ ⟩↦⟨ s₁ , σ ⟩
   if-FS : ∀ {s₁ s₂ σ b} → F (⟦ b ⟧ᵉ σ) → ⟨ if b then s₁ else s₂ , σ ⟩↦⟨ s₂ , σ ⟩
   -- whileS : ∀ {s σ b} → ⟨ while b [ s ] , σ ⟩↦⟨ (if b then (s , while b [ s ]) else skip) , σ ⟩
   while-TS : ∀ {s σ b} → T (⟦ b ⟧ᵉ σ) → ⟨ while b [ s ] , σ ⟩↦⟨ (s , while b [ s ]) , σ ⟩
   while-FS : ∀ {s σ b} → F (⟦ b ⟧ᵉ σ) → ⟨ while b [ s ] , σ ⟩↦ σ

 -- Derivaciones
 data ⟨_,_⟩_↦[_,_] {n : ℕ} : Stm n → State n → ℕ → Maybe (Stm n) → State n → Set where
   pause : ∀ {s σ} → ⟨ s , σ ⟩ 0 ↦⟨ s , σ ⟩
   _stop : ∀ {s σ σ₁} → ⟨ s , σ ⟩↦ σ₁ → ⟨ s , σ ⟩ 1 ↦ σ₁
   _::_ : ∀ {s₁ s₂ s₃ σ σ₁ σ₂ k} → ⟨ s₁ , σ ⟩↦⟨ s₂ , σ₁ ⟩ → ⟨ s₂ , σ₁ ⟩ k ↦[ s₃ , σ₂ ]
          → ⟨ s₁ , σ ⟩ suc k ↦[ s₃ , σ₂ ]

 -- detS : ∀ {n}{s : Stm n}{s' s'' σ σ₁ σ₂} →
 --                  ⟨ s , σ ⟩↦[ s' , σ₁ ] →
 --                  ⟨ s , σ ⟩↦[ s'' , σ₂ ] →
 --                  s' ≡ s'' × σ₁ ≡ σ₂
 --
 -- detS a b = ?
