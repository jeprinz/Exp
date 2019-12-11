open import Data.Nat

{-
For next time, its time to reason philosophically about what has to be defined
in what order.
Also what would the file look like with all of the self reference just built in.
-}

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

promoteType : ∀ {n} → {Γ : Context} → Index Γ {n} → expU n Γ

-- an  Exp {n} Γ T    is the set of expressions of type T. T must be an element of Uₙ
data Exp : {n : ℕ} → (Γ : Context') → expU n Γ → Set where
  U : (n : ℕ) → ∀ {Γ} → Exp Γ (U' (suc n))
  Var : ∀ {Γ} → ∀ {n} → (i : Index Γ {n}) → Exp {n} Γ (promoteType {n} {Γ} i)

  -- Lambda : ∀ {n} → ∀ {Γ} → ∀ {A} → ∀ {B} → Exp {n} (ConsCtx Γ A) B → Exp Γ (Pi {n} A B)
  -- App : ∀ {n} → ∀ {Γ} → ∀ {A} → ∀ {B} → Exp {n} Γ (Pi {n} A B) → (x : Exp Γ A) →
    -- Exp Γ ({!   !}) -- In the hole, put the substitution of x in B

{-
We want to make sure that there is always only one element
representing (U 4) of e.g.
Exp Γ (U 5), where Γ is nonempty.
-}
--weakenValue isnt enough, consider Lambda. We really need full-on permutations.

expU n Γ = Exp Γ (U' n) --it is necessary that this is defined before promoteType

--TODO: really, we are going to need promoteValue, more general version.
--TODO: maybe with more general version the pattern matching will work?
weakenType : ∀ {n} → ∀ {Γ} → ∀ {A} → expU n Γ → expU n (ConsCtx {n} Γ A)
weakenValue : ∀ {Γ} → ∀ {T} → ∀ {A} → Exp Γ T → Exp (ConsCtx Γ A) (weakenType A)
weakenValue {Γ} {T} {A} e = {! T  !}
weakenType = {!   !}
-- promoteType .{suc n} .{(ConsCtx Γ (U n))} (It {Γ} .{suc n} {U n}) = U n
-- promoteType {n} {Γ'} (It {Γ} {n'} {Var i}) = ?
-- promoteType (Back {T = (U n)} i) = U n
-- promoteType (Back {T = (Var i)} i) = ?
promoteType = {!   !}

U' = U --it is necessary that this is defined after promoteType



-- what all of this has created is:
-- Exp : {n : ℕ} → (Γ : Context) → Exp Γ (U n) → Set
-- U : (n : ℕ) → ∀ {Γ} → Exp Γ (U (suc n))

-- promoteType {n} .(ConsCtx {n} Γ (U n {Γ})) (It {Γ} {.n} {U' .n {.Γ}}) = Exp
-- promoteType {n} (ConsCtx Γ T) (It {.Γ} {.n} {.T}) = {!   !}
-- promoteType {n} (ConsCtx _ _) (Back i) = {!   !}
