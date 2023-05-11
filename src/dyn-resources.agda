{-# OPTIONS --without-K --safe #-}
open import Categories.Category


module dyn-resources {o ℓ e} (𝓥 : Category o ℓ e) where

open import Level
open import Data.Product using (_,_; curry′)

open import Categories.Morphism 𝓥 using (_≅_)
open import Categories.Functor using (Functor)
open import Categories.Functor.Bifunctor

private
  module 𝓥 = Category 𝓥



open 𝓥 hiding (id; identityˡ; identityʳ; assoc)
open Commutation 𝓥
open Definitions 𝓥



variable  j k l : Level

-- Defining a symmetric monoidal category
-- record SymmetricMonoidalCategory {i j k} {U V W X : Set i} (𝓥 : Category i j k ) (⊗ : Bifunctor 𝓥 𝓥 𝓥) (unit : Set i) : Set ( i ⊔ j ⊔ k) where
--   infixr 10  _⊗₀_ 
--   field
--    _⊗₀_ : Set i → Set i → 𝓥 
--   field
--     associator : ∀ {U V W X : Set i } → (U ⊗₀ V) ⊗₀ W ≅ U ⊗₀ (V ⊗₀ W)
--     l-unitor : 𝓥 → 𝓥
--     r-unitor : 𝓥 → 𝓥
--     symmetor : 𝓥 → 𝓥

private
  variable
    U V W X Y A B : Obj
    f g h i a b : X ⇒ Y

-- Defining SymmetricMonoidal

record SymmetricMonoidal : Set (o ⊔ ℓ ⊔ e) where
  field
    ⊗ : Bifunctor 𝓥 𝓥 𝓥
    ∘ : Bifunctor  𝓥 𝓥 𝓥
    unit : Obj

  module ⊗ = Functor ⊗
  open Functor ⊗

  _⊗₀_ : Obj → Obj → Obj
  _⊗₀_ = curry′ F₀

  field
    unitorʳ : unit ⊗₀ X ≅ X
    unitorˡ : X ⊗₀ unit ≅ X
    associator : U ⊗₀ (V ⊗₀ W) ≅ (U ⊗₀ V) ⊗₀ W
    symmetor : U ⊗₀ W ≅ W ⊗₀ U
    
