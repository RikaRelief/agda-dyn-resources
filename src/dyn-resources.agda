{-# OPTIONS --without-K --safe #-}
open import Categories.Category


module dyn-resources {o ℓ e} (𝓥 : Category o ℓ e) where

open import Level
open import Data.Product using (_,_; curry′)

open import Categories.Morphism 𝓥 using (_≅_)
open import Categories.Functor using (Functor) 
open import Categories.Functor.Bifunctor using (Bifunctor; appˡ; appʳ)

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
--    _⊗₀_ : Set i → Set i → Set i
--   field
--     associator : ∀ {U V W X : Set i } → (U ⊗₀ V) ⊗₀ W ≅ U ⊗₀ (V ⊗₀ W)
--     l-unitor : 𝓥 → 𝓥
--     r-unitor : 𝓥 → 𝓥
--     symmetor : 𝓥 → 𝓥

private
  variable
    U V W X Y Z A B : Obj
    f g h i a b : X ⇒ Y

-- Defining SymmetricMonoidal this definition is adapted from the agda-categories library 

record SymmetricMonoidal : Set (o ⊔ ℓ ⊔ e) where
  infixr 10 _⊗₀_
  
  field
    -- You can think of this as parallel resource composition
    ⊗ : Bifunctor 𝓥 𝓥 𝓥
    -- This could be thought of as sequential resource composition
    ∘₁ : Bifunctor  𝓥 𝓥 𝓥
    -- This is the void resource
    unit : Obj
    -- The hom-set 𝓥(Obj₁, Obj₂) represents transformations of resource Obj₁ into resource Obj₂
    -- that can be implemented without any cost

  module ⊗ = Functor ⊗
  open Functor ⊗

  _⊗₀_ : Obj → Obj → Obj
  _⊗₀_ = curry′ F₀

  -- this is also 'curry', but a very-dependent version
  _⊗₁_ : X ⇒ Y → Z ⇒ W → X ⊗₀ Z ⇒ Y ⊗₀ W
  f ⊗₁ g = F₁ (f , g)

  _⊗- : Obj → Functor 𝓥 𝓥
  X ⊗- = appˡ ⊗ X

  -⊗_ : Obj → Functor 𝓥 𝓥
  -⊗ X = appʳ ⊗ X

  field
    unitorʳ : unit ⊗₀ X ≅ X
    unitorˡ : X ⊗₀ unit ≅ X
    associator : U ⊗₀ (V ⊗₀ W) ≅ (U ⊗₀ V) ⊗₀ W
    symmetor : U ⊗₀ W ≅ W ⊗₀ U

  module unitorʳ {X} = _≅_ (unitorʳ {X = X})
  module unitorˡ {X} = _≅_ (unitorˡ {X = X})
  module associator {W} {X} {Y} = _≅_ (associator {W} {X} {Y})
  module symmetor {U} {W} = _≅_ (symmetor {U} {W})

  CommutativeSquare′ : {A B C D : Obj} → (f : A ⇒ B) (g : A ⇒ C) (h : B ⇒ D) (i : C ⇒ D) → Set _
  CommutativeSquare′ f g h i = h ∘ f ≈ i ∘ g

    
-- Proving the coherence conditions
-- This will mostly follow the proofs provided by rhiel in the category theory in context and also from the Mac lane book
-- Categories for the working mathematician
-- The commutativity of the monoidal product can also be shown by braiding

  private
     λ′⇒ = unitorˡ.from
     λ′⇐ = unitorˡ.to
     ρ⇒ = unitorʳ.from
     ρ⇐ = unitorʳ.to
     α⇒ = λ {W} {X} {Y} → associator.from {W} {X} {Y}
     α⇐ = λ {W} {X} {Y} → associator.to {W} {X} {Y}
     γ⇒ = λ {U} {W}     → symmetor.from {U} {W}
     γ⇐ = λ {U} {W}     → symmetor.from {U} {W}

  field
    unitorˡ-commute-from : CommutativeSquare (𝓥.id ⊗₁ f)  λ′⇒ λ′⇒ f
    unitorˡ-commute-to   : CommutativeSquare f λ′⇐ λ′⇐ (𝓥.id ⊗₁ f)
    unitorʳ-commute-from : CommutativeSquare (f ⊗₁ 𝓥.id) ρ⇒ ρ⇒ f
    unitorʳ-commute-to   : CommutativeSquare  f ρ⇐ ρ⇐ (f ⊗₁ 𝓥.id)
    assoc-commute-from  : CommutativeSquare ((f ⊗₁ g) ⊗₁ h) α⇒ α⇒ (f ⊗₁ (g ⊗₁ h))
    assoc-commute-to    : CommutativeSquare (f ⊗₁ (g ⊗₁ h)) α⇐ α⇐ ((f ⊗₁ g) ⊗₁ h)
    triangle            : [ (X ⊗₀ unit) ⊗₀ Y ⇒ X ⊗₀ Y ]⟨
                            α⇒           ⇒⟨ X ⊗₀ (unit ⊗₀ Y) ⟩
                            𝓥.id ⊗₁ λ′⇒
                          ≈ ρ⇒ ⊗₁ 𝓥.id
                          ⟩
    pentagon            : [ ((X ⊗₀ Y) ⊗₀ Z) ⊗₀ W ⇒ X ⊗₀ Y ⊗₀ Z ⊗₀ W ]⟨
                            α⇒ ⊗₁ 𝓥.id     ⇒⟨ (X ⊗₀ Y ⊗₀ Z) ⊗₀ W ⟩
                            α⇒              ⇒⟨ X ⊗₀ (Y ⊗₀ Z) ⊗₀ W ⟩
                            𝓥.id ⊗₁ α⇒
                          ≈ α⇒              ⇒⟨ (X ⊗₀ Y) ⊗₀ Z ⊗₀ W ⟩
                            α⇒
                          ⟩
    hexagon             : [ (X ⊗₀ Y) ⊗₀ Z ⇒ Y ⊗₀ Z ⊗₀ X ]⟨
                            α⇒             ⇒ ⟨ X ⊗₀ (Y ⊗₀ Z) ⟩
                            γ⇒             ⇒ ⟨ (Y ⊗₀ Z) ⊗₀ X ⟩
                            α⇒             ⇒ ⟨ Y ⊗₀ (Z ⊗₀ Z) ⟩
                          ≈ γ⇒ ⊗₁ 𝓥.id   ⇒ ⟨ (Y ⊗₀ X) ⊗₀ Z ⟩
                            α⇒             ⇒ ⟨ Y ⊗₀ (X ⊗₀ Z) ⟩
                            𝓥.id ⊗₁ γ⇒   ⇒ ⟨ Y ⊗₀ (Z ⊗₀ X) ⟩
                          ⟩ 
                            
       


