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
  -- Var : ∀ {Γ} → ∀ {n} → (i : Index Γ {n}) → Exp {n} Γ (promoteType Γ i)

  -- Lambda : ∀ {n} → ∀ {Γ} → ∀ {A} → ∀ {B} → Exp {n} (ConsCtx Γ A) B → Exp Γ (Pi {n} A B)
  -- App : ∀ {n} → ∀ {Γ} → ∀ {A} → ∀ {B} → Exp {n} Γ (Pi {n} A B) → (x : Exp Γ A) →
    -- Exp Γ ({!   !}) -- In the hole, put the substitution of x in B


expU n Γ = Exp Γ (U' n)
U' = U
-- what all of this has created is:
-- Exp : {n : ℕ} → (Γ : Context) → Exp Γ (U n) → Set
-- U : (n : ℕ) → ∀ {Γ} → Exp Γ (U (suc n))

-- U U' ??????
implImpl : ∀ {n} → ∀ {Γ} → (T : Exp Γ (U n)) → Exp (ConsCtx Γ T) (U n)
implImpl (U n) = {!   !}

promoteTypeImpl : ∀ {n} → (Γ : Context) → Index Γ {n} → Exp Γ (U n)
promoteTypeImpl .(ConsCtx _ _) (It {Γ} {n} {T}) = {!   !}
promoteTypeImpl .(ConsCtx _ _) (Back i) = {!   !}

promoteType = {!   !}
-- promoteType {n} .(ConsCtx {n} Γ (U n {Γ})) (It {Γ} {.n} {U' .n {.Γ}}) = Exp
-- promoteType {n} (ConsCtx Γ T) (It {.Γ} {.n} {.T}) = {!   !}
-- promoteType {n} (ConsCtx _ _) (Back i) = {!   !}
