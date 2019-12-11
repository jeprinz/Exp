open import Data.Nat

{-
This file is a slightly different idea about how constructors of Exp should work
The idea is that e.g. U only works in the empty context, but then
there is a constructor Weaken which goes Exp Γ T → Exp (ConsCtx Γ A) (promoteType T)
and then promoteType is just defined with Weaken.
Question: does this lead to redundancy?
-}

Context' : Set
expU : (n : ℕ) → (Γ : Context') → Set -- expU {n} Γ = Exp {n} Γ (U n)

data Context : Set where
  ∅ : Context
  ConsCtx : ∀ {n} → (Γ : Context') → expU n Γ → Context
Context' = Context

U' : (n : ℕ) → ∀ {Γ} → expU (suc n) Γ -- U' = U
--given the above meaning of expU,   U': (n : ℕ) → ∀ {Γ} → Exp {suc n} Γ (U (suc n))

WeakenType : ∀ {n m} → ∀ {Γ} → ∀ {A} → expU n Γ → expU n (ConsCtx {m} Γ A)

-- an  Exp {n} Γ T    is the set of expressions of type T. T must be an element of Uₙ
data Exp : {n : ℕ} → (Γ : Context') → expU n Γ → Set where
  U : (n : ℕ) → Exp ∅ (U' (suc n))
  -- U : (n : ℕ) → ∀ {Γ} → Exp Γ (U' (suc n)) -- redundancy with Weaken, but just rolling with it for now
  InCtx : ∀ {n} → ∀ {Γ} → ∀ {T} → Exp {n} (ConsCtx Γ T) (WeakenType T)
  Weaken : ∀ {n m} → ∀ {Γ} → ∀ {T} → ∀ {A} → Exp {n} Γ T → Exp {n} (ConsCtx {m} Γ A) (WeakenType {n} T)

  -- Lambda : ∀ {n} → ∀ {Γ} → ∀ {A} → ∀ {B} → Exp {n} (ConsCtx Γ A) B → Exp Γ (Pi {n} A B)
  -- App : ∀ {n} → ∀ {Γ} → ∀ {A} → ∀ {B} → Exp {n} Γ (Pi {n} A B) → (x : Exp Γ A) →
    -- Exp Γ ({!   !}) -- In the hole, put the substitution of x in B

expU n Γ = Exp Γ (U' n)
-- U' n {∅} = U n
-- U' n {ConsCtx Γ x} = {!   !}
U' n {∅} = U n
U' n {ConsCtx {m} Γ T} = WeakenType {suc n} {m} {Γ} {T} (U' n {Γ})
WeakenType = Weaken
-- what all of this has created is:
-- Exp : {n : ℕ} → (Γ : Context) → Exp Γ (U n) → Set
-- U : (n : ℕ) → ∀ {Γ} → Exp Γ (U (suc n))
