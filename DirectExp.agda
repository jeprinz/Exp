open import Data.Nat

Context' : Set
expU : (n : ℕ) → (Γ : Context') → Set -- expU {n} Γ = Exp {n} Γ (U n)

data Context : Set where
  ∅ : Context
  ConsCtx : ∀ {n} → (Γ : Context') → expU n Γ → Context
Context' = Context

U' : (n : ℕ) → ∀ {Γ} → expU (suc n) Γ -- U' = U
--given the above meaning of expU,   U': (n : ℕ) → ∀ {Γ} → Exp {suc n} Γ (U (suc n))

data Index : Context → {n : ℕ} → Set where -- defines a position in a context
  It : ∀ {Γ} → ∀ {n} → {T : expU n Γ} → Index (ConsCtx Γ T) {n}
  Back : ∀ {Γ} → ∀ {n m} → {T : expU n Γ} → Index Γ {m} → Index (ConsCtx {n} Γ T) {n}

promoteType : ∀ {n} → (Γ : Context) → Index Γ {n} → expU n Γ

-- an  Exp {n} Γ T    is the set of expressions of type T. T must be an element of Uₙ
data Exp : {n : ℕ} → (Γ : Context') → expU n Γ → Set where
  U : (n : ℕ) → ∀ {Γ} → Exp Γ (U' (suc n))
  Var : ∀ {Γ} → ∀ {n} → (i : Index Γ {n}) → Exp {n} Γ (promoteType Γ i)
  -- Lambda : ∀ {n} → ∀ {Γ} → ∀ {A} → ∀ {B} → Exp {n} (ConsCtx Γ A) B → Exp Γ (Pi {n} A B)
  -- App : ∀ {n} → ∀ {Γ} → ∀ {A} → ∀ {B} → Exp {n} Γ (Pi {n} A B) → (x : Exp Γ A) →
    -- Exp Γ ({!   !}) -- In the hole, put the substitution of x in B

{-
TODO: problem (but I know how to fix it but it will be hard)
In a non-empty context, U is a type, but also (WeakerCtx U) is a type.
This is a problem, there should only be one U and its messing things up.
The intuition is that only InCtx should be used after WeakerCtx.
The solution is to remove both InCtx and WeakerCtx and replace with one constructor,
InCtx (yup the same name as before) which inputs a proof that the type is in the
context.

We need:
weakerCtx U = U
weakerCtx (Lambda e) = Lambda (weakenCtx e)
weakerCtx (InCtx n) =  (InCtx (n + 1))

Problem: example:
Let T : Exp ∅ (U 0). Consider Γ = [T]. I want an element of Exp [T] ?
where ? "=" T. But ? cant be T because T is in empty context.
-}

expU n Γ = Exp Γ (U' n)
U' = U
-- what all of this has created is:
-- Exp : {n : ℕ} → (Γ : Context) → Exp Γ (U n) → Set
-- U : (n : ℕ) → ∀ {Γ} → Exp Γ (U (suc n))

promoteType (ConsCtx _ (U n)) It = {!   !}
promoteType (ConsCtx _ T) It = {!   !}
promoteType (ConsCtx _ _) (Back i) = {!   !}
