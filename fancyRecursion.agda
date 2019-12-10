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
Example' : exampleex → Set
ex' : exampleex

data Example : exampleex → Set where
  ex : Example ex'

exampleex = Example' ex'
Example' = Example
ex' = ex

-- ^ from reddit https://www.reddit.com/r/agda/comments/b9ni7l/another_beginner_question_how_to_define_mutually/

--try a church encoding
-- Example : Example ex → Set
-- Example ex = (C : C ex → Set) → (C ex) → C ex

-- ex : Example ex
-- ex C ex' = ex'

-- In this case, Example = 𝟙. ex untyped is just identity function
-- lets try stripping types from Exp and see what happens.

--church encoding of Exp:
-- Exp : {n : ℕ} → (Γ : Context) → Exp {n} Γ U → Set
-- Exp {n₀} Γ­₀ T₀ = (C : {n : ℕ} → (Γ : Context) → C {n} Γ U) →
  -- ((n : ℕ) → ∀ {Γ} → C {suc n} Γ (U (suc n))) → C n₀ Γ₀ T₀

-- U : (n : ℕ) → Exp {suc n} Γ (U (suc n))
-- U n C u = u n

--so, untyped, U is just U n = λ u . u n
-- Exp n Γ = 𝟙

--Question: how to make church encoding of the following types

mutual
  data A : Set where
    a : A

  data B : A → Set where
    b : B a
