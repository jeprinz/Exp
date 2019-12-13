open import Data.Nat
open import Agda.Primitive

-- data Example : Example ex → Set where
  -- ex : Example ex

exampleex : Set lzero
ex' : exampleex

data Example : exampleex → Set lzero where
  ex : Example ex'

exampleex = Example ex'
ex' = ex

test : (e : Example ex) → Example e → ℕ
test e ex = 0
