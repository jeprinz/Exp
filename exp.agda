open import Data.Nat

max : ℕ → ℕ → ℕ -- move this elsewhere later...
max zero m = m
max (suc n) zero = suc n
max (suc n) (suc m) = suc (max n m)

-- Need to declare some types up front for eventual self reference
Context' : Set --later on, Context' = Context
expU : (n : ℕ) → (Γ : Context') → Set -- later on, expU {n} Γ = Exp {n} Γ (U n)

data Context : Set where -- A list of types
  ∅ : Context
  ConsCtx : ∀ {n} → (Γ : Context') → expU n Γ → Context
Context' = Context

U' : (n : ℕ) → ∀ {Γ} → expU (suc n) Γ -- later on, U' = U
--given the above meaning of expU,   U': (n : ℕ) → ∀ {Γ} → Exp {suc n} Γ (U (suc n))
Pi' : ∀ {n m} → ∀ {Γ} → (A : expU n Γ) → (B : expU m (ConsCtx Γ A)) → expU (suc (max n m)) Γ --Pi' = Pi
WeakenType : ∀ {n m} → ∀ {Γ} → ∀ {A} → expU n Γ → expU n (ConsCtx {m} Γ A)
Exp' : {n : ℕ} → (Γ : Context') → expU n Γ → Set
substType : ∀ {n m Γ A} → expU n (ConsCtx Γ A) → Exp' {m} Γ A → expU n Γ

-- an  Exp {n} Γ T    is the set of expressions of type T. T must be an element of Uₙ
data Exp : {n : ℕ} → (Γ : Context') → expU n Γ → Set where
  U : (n : ℕ) → Exp ∅ (U' (suc n))
  InCtx : ∀ {n Γ T} → Exp {n} (ConsCtx Γ T) (WeakenType T)
  Weaken : ∀ {n m Γ T A} → Exp {n} Γ T → Exp {n} (ConsCtx {m} Γ A) (WeakenType {n} T)
  Pi : ∀ {n m Γ} → (A : expU n Γ) → (B : expU m (ConsCtx Γ A)) → Exp Γ (U' (suc (max n m)))
  Lambda : ∀ {n Γ A B} → Exp {n} (ConsCtx Γ A) B → Exp Γ (Pi' {n} A B)
  App : ∀ {n m Γ} → {A : expU n Γ} → {B : expU m (ConsCtx Γ A)} → Exp Γ (Pi' A B) →
    (x : Exp' Γ A) → Exp Γ (substType B x) -- In the hole, put the substitution of x in B

-- Agda crashes when I try to pattern match on Exp, so I need an induction principle.
-- It must be defined before I tie the knot, or else it too would crash Agda.
ind : (P : {n : ℕ} → {Γ : Context} → {T : expU n Γ} → Exp {n} Γ T → Set) →
  ((n : ℕ) → P (U n)) → --U
  (∀ {n Γ T} → P (InCtx {n} {Γ} {T})) → --InCtx
  (∀ {n m  Γ T A} → (e : Exp {n} Γ T) →
    P (Weaken {n} {m} {Γ} {T} {A} e)) → --Weaken
  (∀ {n m Γ} → (A : expU n Γ) → (B : expU m (ConsCtx Γ A)) → P (Pi A B)) → --Pi
  (∀ {n Γ A B} → (e : Exp {n} (ConsCtx Γ A) B) → P (Lambda e)) → --Lambda
  (∀ {n m Γ} → {A : expU n Γ} → {B : expU m (ConsCtx Γ A)} → (f : Exp Γ (Pi' A B)) →
    (x : Exp' Γ A) → P (App f x)) → --App
  {n : ℕ} → {Γ : Context} → {T : expU n Γ} → (e : Exp {n} Γ T) → (P e)
ind P u i w p l a (U n) = u n
ind P u i w p l a (InCtx {n} {Γ} {T}) = i {n} {Γ} {T}
ind P u i w p l a (Weaken {n} {m} {Γ} {T} {A} e) = w {n} {m} {Γ} {T} {A} e
ind P u i w p l a (Pi A B) = p A B
ind P u i w p l a (Lambda e) = l e
ind P u i w p l a (App f x) = a f x

-- throw in a recursor why not
rec : {Out : Set} →
  ((n : ℕ) → Out) → --U
  ({n : ℕ} → {Γ : Context} → {T : expU n Γ} → Out) → --InCtx
  ({n m : ℕ} → {Γ : Context} → {T : expU n Γ} → {A : expU m Γ} → Exp {n} Γ T → Out) → --Weaken
  (∀ {n m Γ} → (A : expU n Γ) → (B : expU m (ConsCtx Γ A)) → Out) → --Pi
  (∀ {n Γ A B} → Exp {n} (ConsCtx Γ A) B → Out) → --Lambda
  (∀ {n m Γ} → {A : expU n Γ} → {B : expU m (ConsCtx Γ A)} → (f : Exp Γ (Pi' A B)) →
    (x : Exp' Γ A) → Out) → --App
  {n : ℕ} → {Γ : Context} → {T : expU n Γ} → Exp {n} Γ T → Out
rec {Out} = ind (λ e → Out)

-- now, time to tie the knot and make Exp fully defined.
Exp' = Exp -- TODO: might help when defining ind later to move the up?
expU n Γ = Exp Γ (U' n)
U' n {∅} = U n
U' n {ConsCtx {m} Γ T} = WeakenType {suc n} {m} {Γ} {T} (U' n {Γ})
Pi' = Pi
WeakenType = Weaken
-- what all of this has created is:
-- Exp : {n : ℕ} → (Γ : Context) → Exp Γ (U n) → Set
-- U : (n : ℕ) → ∀ {Γ} → Exp Γ (U (suc n))

subst : ∀ {n m Γ A T} → Exp {n} (ConsCtx Γ A) (WeakenType T) → Exp {m} Γ A → Exp {n} Γ T
subst f x = {!   !} -- really, I'm going to need full on permutations of contexts.
                    -- see implementation of permutations from old version.
                    -- I may not need full on permutations, just sublists.
substType = subst

--testing it out a little:
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
