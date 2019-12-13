open import Data.Nat

Context' : Set
expU : (n : ℕ) → (Γ : Context') → Set -- expU {n} Γ = Exp {n} Γ (U n)

data Context : Set where
  ∅ : Context
  ConsCtx : ∀ {n} → (Γ : Context') → expU n Γ → Context
Context' = Context

U' : (n : ℕ) → ∀ {Γ} → expU (suc n) Γ -- U' = U
--given the above meaning of expU,   U': (n : ℕ) → ∀ {Γ} → Exp {suc n} Γ (U (suc n))
Pi' : ∀ {n} → ∀ {Γ} → (A : expU n Γ) → (B : expU n (ConsCtx Γ A)) → expU (suc n) Γ
WeakenType : ∀ {n m} → ∀ {Γ} → ∀ {A} → expU n Γ → expU n (ConsCtx {m} Γ A)

-- an  Exp {n} Γ T    is the set of expressions of type T. T must be an element of Uₙ
data Exp : {n : ℕ} → (Γ : Context') → expU n Γ → Set where
  U : (n : ℕ) → Exp ∅ (U' (suc n))
  InCtx : ∀ {n} → ∀ {Γ} → ∀ {T} → Exp {n} (ConsCtx Γ T) (WeakenType T)
  Weaken : ∀ {n m} → ∀ {Γ} → ∀ {T} → ∀ {A} → Exp {n} Γ T → Exp {n} (ConsCtx {m} Γ A) (WeakenType {n} T)
  Pi : ∀ {n} → ∀ {Γ} → (A : expU n Γ) → (B : expU n (ConsCtx Γ A)) → Exp Γ (U' (suc n))
  -- Pi is not as well tested yet.

  Lambda : ∀ {n} → ∀ {Γ} → ∀ {A} → ∀ {B} → Exp {n} (ConsCtx Γ A) B → Exp Γ (Pi' {n} A B)
  -- App : ∀ {n} → ∀ {Γ} → ∀ {A} → ∀ {B} → Exp {n} Γ (Pi {n} A B) → (x : Exp Γ A) →
    -- Exp Γ ({!   !}) -- In the hole, put the substitution of x in B


-- Agda crashes when I try to pattern match on Exp, so I need an induction principle.
-- It must be defined before I tie the knot, or else it too would crash Agda.
ind : (P : {n : ℕ} → {Γ : Context} → {T : expU n Γ} → Exp {n} Γ T → Set) →
  ((n : ℕ) → P (U n)) → --U
  ({n : ℕ} → {Γ : Context} → {T : expU n Γ} → P (InCtx {n} {Γ} {T})) → --InCtx
  ({n m : ℕ} → {Γ : Context} → {T : expU n Γ} → {A : expU m Γ} → (e : Exp {n} Γ T) →
    P (Weaken {n} {m} {Γ} {T} {A} e)) → --Weaken
  (∀ {n} → ∀ {Γ} → (A : expU n Γ) → (B : expU n (ConsCtx Γ A)) → P (Pi A B)) → --Pi
  (∀ {n} → ∀ {Γ} → ∀ {A} → ∀ {B} → (e : Exp {n} (ConsCtx Γ A) B) → P (Lambda e)) → --Lambda
  {n : ℕ} → {Γ : Context} → {T : expU n Γ} → (e : Exp {n} Γ T) → (P e)
ind P u i w p l (U n) = u n
ind P u i w p l (InCtx {n} {Γ} {T}) = i {n} {Γ} {T}
ind P u i w p l (Weaken {n} {m} {Γ} {T} {A} e) = w {n} {m} {Γ} {T} {A} e
ind P u i w p l (Pi A B) = p A B
ind P u i w p l (Lambda e) = l e

rec : {Out : Set} →
  ((n : ℕ) → Out) → --U
  ({n : ℕ} → {Γ : Context} → {T : expU n Γ} → Out) → --InCtx
  ({n m : ℕ} → {Γ : Context} → {T : expU n Γ} → {A : expU m Γ} → Exp {n} Γ T → Out) → --Weaken
  (∀ {n} → ∀ {Γ} → (A : expU n Γ) → (B : expU n (ConsCtx Γ A)) → Out) → --Pi
  (∀ {n} → ∀ {Γ} → ∀ {A} → ∀ {B} → Exp {n} (ConsCtx Γ A) B → Out) → --Lambda
  {n : ℕ} → {Γ : Context} → {T : expU n Γ} → Exp {n} Γ T → Out
rec {Out} = ind (λ e → Out)

-- now, time to tie the knot and make Exp fully defined.
expU n Γ = Exp Γ (U' n)
U' n {∅} = U n
U' n {ConsCtx {m} Γ T} = WeakenType {suc n} {m} {Γ} {T} (U' n {Γ})
Pi' = Pi
WeakenType = Weaken
-- what all of this has created is:
-- Exp : {n : ℕ} → (Γ : Context) → Exp Γ (U n) → Set
-- U : (n : ℕ) → ∀ {Γ} → Exp Γ (U (suc n))

e : Exp ∅ (Pi (U' 0) (U' 0))
e = Lambda InCtx

e' : Exp ∅ (Pi (U' 1) (U' 1))
e' = Lambda (U' 0)

-- recursor does work in practice!!!!
-- not going to be useful though without induction principle...
-- test : Exp ∅ (Pi (U' 1) (U' 1)) → ℕ
-- test e = rec (λ n → n) --U n, can't happen
--              (2) -- InCtx, note this can't even happen
--              (λ e → rec {!   !} {!   !} {!   !} {!   !} {!   !} e) -- Weaken e, also can't happen
--              (λ A B → rec {!   !} {!   !} {!   !} {!   !} {!   !} B) -- Pi A B, also can't happen
--              (λ e → rec {!   !} {!   !} {!   !} {!   !} {!   !} e) -- Lambda e
--              e
