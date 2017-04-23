module FingerTree.Data.List where

open import Prelude.List

open import FingerTree.Class.Reduce

instance
  ReduceList : ∀ {a} → Reduce {a} List
  Reduce.reducer ReduceList _∙_ FA b = foldr _∙_ b FA
  Reduce.reducel ReduceList _∙_ b FA = foldl _∙_ b FA
