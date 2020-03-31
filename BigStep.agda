module BigStep where

 import Data.Bool as Bool using (not)
 open import Data.Bool hiding (not; if_then_else_)
 open import Data.Empty
 open import Data.Fin using (Fin; suc; zero; #_)
 open import Data.Nat
 open import Data.Nat.Properties
 open import Data.Vec
 open import Function
 open import Relation.Nullary
 open import Relation.Binary.PropositionalEquality
 open import Data.Product

 open import Decidable
 open import Grammar


 -- Definimos las reglas de evaluación de la semántica operacional de paso grande

 data ⟨_,_⟩⇒_ {n : ℕ} : Stm n → State n → State n → Set where
    assB : ∀ {x a σ} → ⟨ x := a , σ ⟩⇒  (σ [ x ]≔ ⟦ a ⟧ᵉ σ)
    skipB : ∀ {σ} → ⟨ skip , σ ⟩⇒ σ
    compB : ∀ {s₁ s₂ σ σ₁ σ₂} → ⟨ s₁ , σ ⟩⇒ σ₁ → ⟨ s₂ , σ₁ ⟩⇒ σ₂ → ⟨ (s₁ , s₂) , σ ⟩⇒ σ₂
    if-TB : ∀ {s₁ s₂ σ σ₁ b} → T (⟦ b ⟧ᵉ σ) → ⟨ s₁ , σ ⟩⇒ σ₁ → ⟨ if b then s₁ else s₂ , σ ⟩⇒ σ₁
    if-FB : ∀ {s₁ s₂ σ σ₁ b} → F (⟦ b ⟧ᵉ σ) → ⟨ s₂ , σ ⟩⇒ σ₁ → ⟨ if b then s₁ else s₂ , σ ⟩⇒ σ₁
    while-TB : ∀ {b s σ σ₁ σ₂} → T (⟦ b ⟧ᵉ σ) → ⟨ s , σ ⟩⇒ σ₁ → ⟨ while b [ s ] , σ₁ ⟩⇒ σ₂ → ⟨ while b [ s ] , σ ⟩⇒ σ₂
    while-FB : ∀ {b s σ} → F (⟦ b ⟧ᵉ σ) → ⟨ while b [ s ] , σ ⟩⇒ σ
 
 detB : ∀ {n}{s : Stm n}{σ σ₁ σ₂} → ⟨ s , σ ⟩⇒ σ₁ → ⟨ s , σ ⟩⇒ σ₂ → σ₁ ≡ σ₂
 detB assB assB =  refl
 detB skipB skipB = refl
 detB (compB a a₁) (compB b b₁)
  rewrite detB a b
   | detB a₁ b₁ = refl
 detB (if-TB x a) (if-TB x₁ b)
  rewrite detB a b = refl
 detB (if-TB x a) (if-FB x₁ b)
  rewrite T→≡true x =  ⊥-elim x₁
 detB (if-FB x a) (if-TB x₁ b)
  rewrite T→≡true x₁ = ⊥-elim x
 detB (if-FB x a) (if-FB x₁ b)
  rewrite detB a b = refl
 detB (while-TB x a a₁) (while-TB x₁ b b₁)
  rewrite detB a b
    | detB a₁ b₁ = refl
 detB (while-TB x a a₁) (while-FB x₁)
  rewrite T→≡true x = ⊥-elim x₁
 detB (while-FB x) (while-TB x₁ b b₁)
  rewrite T→≡true x₁ =  ⊥-elim x
 detB (while-FB x) (while-FB x₁) = refl
