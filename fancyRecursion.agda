-- {-# OPTIONS --without-K #-}
open import Data.Nat
{-The goal of this file is to solve a problem of self reference.

I would like to have a definition like the following:
data Exp : {n : ℕ} → (Γ : Context) → Exp {n} Γ U → Set where
  U : (n : ℕ) → ∀ {Γ} → Exp {suc n} Γ (U (suc n))
  ...
  ...

But there are two places where self reference prohibits this:
1) the use of U in the first line
2) the use of U in the definition of U


A simple example of just (1) could be the following:

data Example : Example ex → Set where
  ex : Example ex

This cannot be defined. Lets try to figure out how!!!
-}

exampleex : Set
ex' : exampleex

data Example : exampleex → Set where
  ex : Example ex'

test : (e : exampleex) → Example e → ℕ
test _ ex = 0

patternMatch : (P : (x : exampleex) → Example x → Set) → (P ex' ex) →
  ((x : exampleex) → (e : Example x) → P x e)
patternMatch P val _ ex = val

exampleex = Example ex'
ex' = ex

test' : (e : Example ex) → Example e → ℕ
test' = patternMatch (λ x e → ℕ) 0


---IMPORTANT: the above function makes agda type checker never terminate.
-- what can be done about this? This whole project can't work without
-- being able to pattern match on Exp.

-- ^ from reddit https://www.reddit.com/r/agda/comments/b9ni7l/another_beginner_question_how_to_define_mutually/
