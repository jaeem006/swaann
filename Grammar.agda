module Grammar where

 import Data.Bool as B using(not) 
 open import Data.Nat 
 open import Data.Bool hiding (not; if_then_else_; _≤_; _<_)
 open import Data.Vec
 open import Data.Fin using (Fin; suc; zero; #_)
 -- Fin es un conjunto de números finitos
 open import Relation.Nullary
 open import Relation.Nullary.Decidable
 open import Decidable
 --open import Relation.Binary.PropositionalEquality

 -- Definimos los tipos del lenguaje WHILE
 
 -- Notemos que estamos utilzando Naturales en lugar de Enteros pues facilita las demostraciones
 -- y manejar enteros en Agda no es trivial.

 data Type : Set where
   nat bool : Type

 -- Se definen las interpretaciones de los valores del lenguaje WHILEa naturales y booleanos
 -- de Agda
 ⟦_⟧ᵗ : Type → Set
 ⟦ nat  ⟧ᵗ = ℕ
 ⟦ bool ⟧ᵗ = Bool
 
 -- Para representar los estados usamos indices de deBruijn y vectores, el valor de la variable n
 -- es el valor que se encuentre en el inidce n del vector

 State : ℕ → Set 
 State = Vec ℕ

 -- Está es una bonita forma de hacer sinónimos en Agda.

 -- Definimos las expresiones del lenguaje, aritméticas y booleanas juntas por
 -- simplicidad. Se define como un tipo dependiente de un natural n para construir
 -- el estado en el caso de las variables
 data ABE (n : ℕ) : Type → Set where
     Num : ℕ → ABE n nat
     add mul sub : ABE n nat → ABE n nat → ABE n nat
     var : Fin n → ABE n nat
     #t #f : ABE n bool
     eq le lt : ABE n nat → ABE n nat → ABE n bool
     and : ABE n bool → ABE n bool → ABE n bool
     not : ABE n bool → ABE n bool
     
 infixr 5 _:=_
 infixr 4 _,_

 -- Definimos ahora los enunciados del lenguaje WHILE, también dependientes del tamaño
 -- del estado, esto se puede pues ninguna operación cambia el tamaño. Suponemos que
 -- la asiganción dunciona unicamente con variables que ya están en el estado.
 data Stm (n : ℕ) : Set where
      _:=_ : Fin n → ABE n nat → Stm n
      skip : Stm n
      _,_ : Stm n → Stm n → Stm n
      if_then_else_ : ABE n bool → Stm n → Stm n → Stm n
      while_[_] : ABE n bool → Stm n → Stm n
      
 -- Definimos la semántica del lenguaje
 ⟦_⟧ᵉ : ∀ {n t} → ABE n t → State n → ⟦ t ⟧ᵗ
 ⟦ Num x ⟧ᵉ _ = x
 ⟦ add a b ⟧ᵉ σ = ⟦ a ⟧ᵉ σ + ⟦ b ⟧ᵉ σ
 ⟦ mul a b ⟧ᵉ σ = ⟦ a ⟧ᵉ σ * ⟦ b ⟧ᵉ σ
 ⟦ sub a b ⟧ᵉ σ = ⟦ a ⟧ᵉ σ ∸ ⟦ b ⟧ᵉ σ
 ⟦ var x ⟧ᵉ σ = lookup (σ) x
 ⟦ #t ⟧ᵉ _  = true
 ⟦ #f ⟧ᵉ _ = false
 ⟦ eq  a b ⟧ᵉ σ = ⌊ ⟦ a ⟧ᵉ σ ≡⁇ ⟦ b ⟧ᵉ σ ⌋
 ⟦ le a b ⟧ᵉ σ = ⌊ ⟦ a ⟧ᵉ σ ≤⁇ ⟦ b ⟧ᵉ σ ⌋
 ⟦ lt  a b ⟧ᵉ σ = ⌊ ⟦ a ⟧ᵉ σ <⁇ ⟦ b ⟧ᵉ σ ⌋
 ⟦ and a b ⟧ᵉ σ =   ⟦ a ⟧ᵉ σ ∧  ⟦ b ⟧ᵉ σ 
 ⟦ not e   ⟧ᵉ σ = B.not (⟦ e ⟧ᵉ σ)
