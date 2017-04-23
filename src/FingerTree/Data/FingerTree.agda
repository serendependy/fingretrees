
module FingerTree.Data.FingerTree where

open import Prelude
open import Tactic.Nat
open import FingerTree.Data.BList
open import FingerTree.Data.FList
open import FingerTree.Data.SeqView
open import FingerTree.Data.List
open import FingerTree.Class.Reduce

Node : ∀ {a} (A : Set a) → Set a
Node A = FList A 2 3

Digit : ∀ {a} (A : Set a) → Set a
Digit A = FList A 1 4

nodeToDigit : ∀ {a} {A : Set a}
              → Node A → Digit A
nodeToDigit n = flpromote 1 ∘ fldemote 1 $ n

{-# DISPLAY FList A 2 3 = Node A #-}
{-# DISPLAY FList A 1 4 = Digit A #-}

data FingerTree {a} (A : Set a) : Set a where
  []      : FingerTree A
  ft[_]   : (a : A) → FingerTree A
  _l∷_∷r_ : (dl : Digit A) → (ft : FingerTree (Node A)) → (dr : Digit A) → FingerTree A

private
  ftreducer : ∀ {a} {A B : Set a} →
              (A → B → B) → FingerTree A → B → B
  ftreducer _∙_ [] b
    = b
  ftreducer _∙_ ft[ a ] b
    = a ∙ b
  ftreducer _∙_ (dl l∷ xs ∷r dr) b
    = let _∙'_ = reducer _∙_
          _∙“_ = ftreducer (reducer _∙_)
      in dl ∙' (xs ∙“ (dr ∙' b))

  ftreducel : ∀ {a} {A B : Set a} →
              (B → A → B) → B → FingerTree A → B
  ftreducel _∙_ b []
    = b
  ftreducel _∙_ b ft[ a ]
    = b ∙ a
  ftreducel _∙_ b (dl l∷ xs ∷r dr)
    = let _∙'_ = reducel _∙_
          _∙“_ = ftreducel (reducel _∙_)
      in ((b ∙' dl) ∙“ xs) ∙' dr

instance
  ReduceFingerTree : ∀ {a} → Reduce (FingerTree {a})
  ReduceFingerTree = record { reducer = ftreducer ; reducel = ftreducel }

infixr 5 _◃_
_◃_ : ∀ {a} {A : Set a} → A → FingerTree A → FingerTree A
a ◃ []
  = ft[ a ]
a ◃ ft[ b ]
  = (a ∷ bl[ [] ]) l∷ [] ∷r (b ∷ bl[ [] ])
a ◃ (dl l∷ ft ∷r dr)
  with flisMax dl
... | left (b ∷ c ∷ d ∷ e ∷ [])
  = (a ∷ bl[ b ∷ [] ])
    l∷ (b ∷ c ∷ bl[ d ∷ [] ]) ◃ ft
    ∷r dr
... | right dl'
  = fldemote 1 (a ∷ dl') l∷ ft ∷r dr

infixl 5 _▹_
_▹_ : ∀ {a} {A : Set a} → FingerTree A → A → FingerTree A
[] ▹ a
  = ft[ a ]
ft[ b ] ▹ a = (b ∷ bl[ [] ]) l∷ [] ∷r (a ∷ bl[ [] ])
(dl l∷ ft ∷r dr) ▹ a with flisMax dr
... | left (e ∷ d ∷ c ∷ b ∷ [])
  = dl
    l∷ ft ▹ (e ∷ d ∷ bl[ c ∷ [] ])
    ∷r (b ∷ bl[ a ∷ [] ])
... | right dr'
  = dl l∷ ft ∷r fldemote 1 (a ∷ dr')

module _ {a} {A : Set a} where

  _◃'_ : {F : Set a → Set a} ⦃ _ : Reduce F ⦄
         → (FA : F A) → FingerTree A → FingerTree A
  _◃'_ = reducer _◃_

  _▹'_ : {F : Set a → Set a} ⦃ _ : Reduce F ⦄
         → FingerTree A → (FA : F A) → FingerTree A
  _▹'_ = reducel _▹_

  reduceToFingerTree : {F : Set a → Set a} ⦃ _ : Reduce F ⦄
                       → (FA : F A) → FingerTree A
  reduceToFingerTree FA = FA ◃' []

ftSeqViewₗ : ∀ {a} {A : Set a}
             → FingerTree A → SeqView FingerTree A
ftdeepₗ : ∀ {a} {A : Set a}
          → FList A 0 3 → FingerTree (Node A) → Digit A → FingerTree A

ftSeqViewₗ []
  = []
ftSeqViewₗ ft[ a ]
  = a ∷ []
ftSeqViewₗ (dl l∷ ft ∷r dr)
  = flhead dl ∷ ftdeepₗ (fltail dl) ft dr

ftdeepₗ bl[ [] ] ft dr
  with ftSeqViewₗ ft
... | []
  = reduceToFingerTree dr
... | x ∷ SA
  = nodeToDigit x l∷ SA ∷r dr
ftdeepₗ (bl[ x ∷ xs ]) ft dr
  = flpromote 1 (x ∷ bl[ xs ]) l∷ ft ∷r dr

module _ {a} {A : Set a} where

  ftisEmpty : FingerTree A → Bool
  ftisEmpty ft with ftSeqViewₗ ft
  ... | []
    = true
  ... | x ∷ SA
    = false

  nodes : ∀ {max}
          → FList A 2 max
          → List (Node A)
  nodes (a ∷ b ∷ bl[ [] ])
    = [ a ∷ b ∷ bl[ [] ] ]
  nodes (a ∷ b ∷ bl[ c ∷ [] ])
    = [ a ∷ b ∷ bl[ c ∷ [] ] ]
  nodes (a ∷ b ∷ bl[ c ∷ d ∷ [] ])
    = (a ∷ b ∷ bl[ [] ]) ∷ (c ∷ d ∷ bl[ [] ]) ∷ []
  nodes (a ∷ b ∷ bl[ c ∷ d ∷ e ∷ xs ])
    = (a ∷ b ∷ bl[ c ∷ [] ]) ∷ nodes (d ∷ e ∷ bl[ xs ])


app3 : ∀ {a} {A : Set a}
       → FingerTree A → List A → FingerTree A → FingerTree A
app3 [] ts ys
  = ts ◃' ys
app3 xs ts []
  = xs ▹' ts
app3 ft[ a ] ts ys
  = a ◃ (ts ◃' ys)
app3 xs ts ft[ a ]
  = (xs ▹' ts) ▹ a
app3 {A = A} (dl₁ l∷ xs ∷r dr₁) ts (dl₂ l∷ ys ∷r dr₂)
  = dl₁ l∷ app3 xs (nodes ns) ys ∷r dr₂
  where
  ns : FList A 2 (4 + (length ts + 4))
  ns
    with (flappendList dr₁ ts)
           ofType FList A (1 + length ts) _
  ... | dr₁++ts
    with (fldemote {min = 1} (length ts) dr₁++ts)
           ofType FList A 1 _
  ... | dr₁++ts'
    = flappend dr₁++ts' dl₂

_▹◃_ : ∀ {a} {A : Set a}
       → (xs ys : FingerTree A) → FingerTree A
xs ▹◃ ys = app3 xs [] ys
