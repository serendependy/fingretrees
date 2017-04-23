
module FingerTree.Data.FList where

open import Prelude
open import FingerTree.Data.BList
open import FingerTree.Class.Reduce

infixr 5 _∷_
data FList {a} (A : Set a) : (min max : Nat) → Set a where
  bl[_] : ∀ {n} → (xs : BList A n) → FList A 0 n
  _∷_   : ∀ {min max} → (x : A) → (xs : FList A min max) → FList A (suc min) (suc max)

private
  flreducer : ∀ {a} {min max} {A B : Set a}
              → (A → B → B) → FList A min max → B → B
  flreducer _∙_ bl[ xs ] b = reducer _∙_ xs b
  flreducer _∙_ (x ∷ xs) b = x ∙ flreducer _∙_ xs b

  flreducel : ∀ {a} {min max} {A B : Set a}
              → (B → A → B) → B → FList A min max → B
  flreducel _∙_ b bl[ xs ] = reducel _∙_ b xs
  flreducel _∙_ b (x ∷ xs) = flreducel _∙_ (b ∙ x) xs

instance
  ReduceFList : ∀ {a min max} → Reduce (λ A → FList {a} A min max)
  ReduceFList = record { reducer = flreducer ; reducel = flreducel }

module _ {a} {A : Set a} where

  open import Tactic.Nat

  flpromote : ∀ {min max} n → FList A min max → FList A min (max + n)
  flpromote n bl[ xs ] = bl[ blpromote n xs ]
  flpromote n (x ∷ xs) = x ∷ flpromote n xs

  fldemotes : ∀ {min max} → FList A (suc min) max → FList A min max
  fldemotes (x ∷ bl[ xs ]) = bl[ x ∷ xs ]
  fldemotes (x ∷ y ∷ xs) = x ∷ fldemotes (y ∷ xs)

  fldemote : ∀ {min max} n → FList A (min + n) max → FList A min max
  fldemote {min} zero xs
    rewrite auto ofType min + 0 ≡ min
    = xs
  fldemote {min} (suc n) xs
    with min + suc n
    |     auto ofType min + suc n ≡ suc min + n
  fldemote {min₁} (suc n) (x ∷ xs)
    | .(suc (min₁ + n)) | refl
    = fldemotes (x ∷ fldemote n xs)

  flisMax : ∀ {min max} → FList A min (suc max) → Either (Vec A (suc max)) (FList A min max)
  flisMax bl[ xs ]
    with blisMax xs
  ... | left xs'
    = left xs'
  ... | right xs'
    = right bl[ xs' ]
  flisMax {max = zero} (x ∷ bl[ [] ]) = left (x ∷ [])
  flisMax {max = suc max₁} (x ∷ bl[ xs ])
    with blisMax xs
  ... | left xs'
    = left (x ∷ xs')
  ... | right xs'
    = right (x ∷ bl[ xs' ])
  flisMax (x ∷ xs'@(y ∷ xs)) with flisMax xs'
  ... | left xs“ = left (x ∷ xs“)
  ... | right xs“ = right (x ∷ xs“)

  flisMin : ∀ {min max} → FList A min max → Either (Vec A min) (FList A (suc min) max)
  flisMin bl[ [] ]
    = left []
  flisMin bl[ x ∷ xs ]
    = right (x ∷ bl[ xs ])
  flisMin (x ∷ xs)
    with flisMin xs
  ... | left xs'
    = left (x ∷ xs')
  ... | right xs'
    = right (x ∷ xs')

  flhead : ∀ {min max} → FList A (suc min) max → A
  flhead (x ∷ xs) = x

  fltail : ∀ {min max} → FList A (suc min) (suc max) → FList A min max
  fltail (x ∷ xs) = xs


  flappendList : ∀ {min max}
                 → FList A min max → (xs : List A)
                 → FList A (min + length xs) (max + length xs)
  flappendList {max = max} bl[ bs ] []
    rewrite auto ofType max + 0 ≡ max
    = bl[ bs ]
  flappendList {max = max} bl[ bs ] (x ∷ xs)
    rewrite auto ofType max + suc (length xs) ≡ suc (max + length xs)
    = x ∷ flappendList bl[ bs ] xs
  flappendList (x ∷ fs) xs = x ∷ flappendList fs xs

  _FL++L_ = flappendList

  flprependBList : ∀ {min max max'}
                  → BList A max' → FList A min max
                  → FList A min (max' + max)
  flprependBList {max = max} {max' = max'} [] fs
    rewrite auto ofType max' + max ≡ max + max'
    = flpromote _ fs
  flprependBList (x ∷ bs) fs = fldemotes (x ∷ flprependBList bs fs)

  flappend : ∀ {min₁ min₂ max₁ max₂}
             → FList A min₁ max₁ → FList A min₂ max₂
             → FList A (min₁ + min₂) (max₁ + max₂)
  flappend bl[ xs ] ys = flprependBList xs ys
  flappend (x ∷ xs) ys = x ∷ flappend xs ys

  _++FL_ = flappend
