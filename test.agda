open import Data.Nat

data ⊥ : Set where

Bad' : Set

data Bad : Set where
  bad : Bad' → Bad

Bad' = Bad
