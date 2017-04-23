
module FingerTree.Class.Reduce where

open import Prelude

record Reduce {a b} (F : Set a → Set b) : Set (lsuc a ⊔ lsuc b) where
  field
    reducer : ∀ {A} {B : Set b} → (_∙_ : A → B → B) → (FA : F A) → (b : B) → B
    reducel : ∀ {A} {B : Set b} → (_∙_ : B → A → B) → (b : B) → (FA : F A) → B

open Reduce ⦃ ... ⦄ public

reduceToList : ∀ {a} {A : Set a} {F : Set a → Set a}
               → ⦃ _ : Reduce F ⦄
               → F A → List A
reduceToList FA = FA ∷' []
  where
    _∷'_ = reducer _∷_
