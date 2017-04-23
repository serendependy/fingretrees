module FingerTree.Data.BList where

open import Prelude
open import FingerTree.Class.Reduce

infixr 5 _∷_
data BList {a} (A : Set a) : Nat → Set a where
  []  : ∀ {n} → BList A n
  _∷_ : ∀ {n} → (x : A) → BList A n → BList A (suc n)

private
  blreducer : ∀ {a n} {A B : Set a} → (A → B → B) → BList A n → B → B
  blreducer _∙_ [] b = b
  blreducer _∙_ (x ∷ xs) b = x ∙ blreducer _∙_ xs b

  blreducel : ∀ {a n} {A B : Set a} → (B → A → B) → B → BList A n → B
  blreducel _∙_ b [] = b
  blreducel _∙_ b (x ∷ xs) = blreducel _∙_ (b ∙ x) xs

instance
  ReduceBList : ∀ {a n} → Reduce (flip (BList {a}) n)
  ReduceBList
    = record { reducer = blreducer ; reducel = blreducel }

module _ {a} {A : Set a} where

  open import Tactic.Nat

  blpromote : ∀ {max} n → BList A max → BList A (max + n)
  blpromote n [] = []
  blpromote n (x ∷ xs) = x ∷ blpromote n xs

  blfromVec : ∀ {m n} → Vec A n → BList A (n + m)
  blfromVec [] = []
  blfromVec (x ∷ xs) = x ∷ blfromVec xs

  blappend : ∀ {max₁ max₂} → BList A max₁ → BList A max₂ → BList A (max₁ + max₂)
  blappend {max₁} {max₂} [] ys
    rewrite auto ofType max₁ + max₂ ≡ max₂ + max₁
    = blpromote max₁ ys
  blappend (x ∷ xs) ys
    = x ∷ blappend xs ys

  bltake : ∀ {max} n → BList A max → BList A n
  bltake zero xs = []
  bltake (suc n) [] = []
  bltake (suc n) (x ∷ xs) = x ∷ bltake n xs

  bldrop : ∀ {max} n → BList A max → BList A (max - n)
  bldrop zero xs = xs
  bldrop (suc n) [] = []
  bldrop (suc n) (x ∷ xs) = bldrop n xs

  blisMax : ∀ {max} → BList A (suc max) → Either (Vec A (suc max)) (BList A max)
  blisMax []
    = right []
  blisMax {zero} (x ∷ [])
    = left (x ∷ [])
  blisMax {suc max₁} (x ∷ xs)
    with blisMax xs
  ... | left xs' = left (x ∷ xs')
  ... | right xs' = right (x ∷ xs')
