
module FingerTree.Data.SeqView where

open import Prelude

data SeqView {a b} (S : Set a → Set b) (A : Set a) : Set (a ⊔ b) where
  []  : SeqView S A
  _∷_ : (x : A) → (SA : S A) → SeqView S A
