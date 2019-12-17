{-# OPTIONS --allow-unsolved-metas #-}
open import Data.Nat

max : ℕ → ℕ → ℕ -- move this elsewhere later...
max zero m = m
max (suc n) zero = suc n
max (suc n) (suc m) = suc (max n m)

-- Need to declare some types up front for eventual self reference
Context' : Set --later on, Context' = Context
valU : (n : ℕ) → (Γ : Context') → Set -- later on, valU {n} Γ = Exp {n} Γ (U n)

data Context : Set where -- A list of types
  ∅ : Context
  ConsCtx : ∀ {n} → (Γ : Context') → valU n Γ → Context
Context' = Context

U' : (n : ℕ) → ∀ {Γ} → valU (suc n) Γ -- later on, U' gives iterated Weaker and U
--given the above meaning of valU,   U': (n : ℕ) → ∀ {Γ} → Exp {suc n} Γ (U (suc n))
Pi' : ∀ {n m} → ∀ {Γ} → (A : valU n Γ) → (B : valU m (ConsCtx Γ A)) → valU (max n m) Γ --Pi' = Pi
WeakenType : ∀ {n m} → ∀ {Γ} → ∀ {A} → valU n Γ → valU n (ConsCtx {m} Γ A)
Value' : {n : ℕ} → (Γ : Context') → valU n Γ → Set
substType : ∀ {n m Γ A} → valU n (ConsCtx Γ A) → Value' {m} Γ A → valU n Γ

-- an  Exp {n} Γ T    is the set of expressions of type T. T must be an element of Uₙ
data UnApplicable : {n : ℕ} → (Γ : Context') → valU n Γ → Set where
  InCtx : ∀ {n Γ T} → UnApplicable {n} (ConsCtx Γ T) (WeakenType T)
  App : ∀ {n m Γ} → {A : valU n Γ} → {B : valU m (ConsCtx Γ A)} → UnApplicable Γ (Pi' A B) →
    (x : Value' Γ A) → UnApplicable Γ (substType B x) -- In the hole, put the substitution of x in B

data Value : {n : ℕ} → (Γ : Context') → valU n Γ → Set where
  U : (n : ℕ) → Value ∅ (U' (suc n))
  Weaken : ∀ {n m Γ T A} → Value {n} Γ T → Value {n} (ConsCtx {m} Γ A) (WeakenType {n} T)
  Pi : ∀ {n m Γ} → (A : valU n Γ) → (B : valU m (ConsCtx Γ A)) → Value Γ (U' (max n m))
  Lambda : ∀ {n m Γ A B} → Value {n} (ConsCtx {m} Γ A) B → Value Γ (Pi' A B)
  fromU : ∀ {n Γ T} → UnApplicable {n} Γ T → Value {n} Γ T

indv : (P : {n : ℕ} → {Γ : Context} → {T : valU n Γ} → Value {n} Γ T → Set) →
  ((n : ℕ) → P (U n)) → --U
  (∀ {n m  Γ T A} → (e : Value {n} Γ T) →
    P (Weaken {n} {m} {Γ} {T} {A} e)) → --Weaken
  (∀ {n m Γ} → (A : valU n Γ) → (B : valU m (ConsCtx Γ A)) → P (Pi A B)) → --Pi
  (∀ {n m Γ A B} → (e : Value {n} (ConsCtx {m} Γ A) B) → P (Lambda e)) → --Lambda
  (∀ {n Γ T} → (u : UnApplicable {n} Γ T) → P (fromU u)) → -- fromU
  {n : ℕ} → {Γ : Context} → {T : valU n Γ} → (e : Value {n} Γ T) → (P e)
indv P u w p l f (U n) = u n
indv P u w p l f (Weaken {n} {m} {Γ} {T} {A} e) = w {n} {m} {Γ} {T} {A} e
indv P u w p l f (Pi A B) = p A B
indv P u w p l f (Lambda e) = l e
indv P u w p l f (fromU un) = f un

indu : (P : {n : ℕ} → {Γ : Context} → {T : valU n Γ} → UnApplicable {n} Γ T → Set) →
  (∀ {n Γ T} → P (InCtx {n} {Γ} {T})) → --InCtx
  (∀ {n m Γ} → {A : valU n Γ} → {B : valU m (ConsCtx Γ A)} → (f : UnApplicable Γ (Pi' A B)) →
    (x : Value' Γ A) → P (App f x)) → --App
  {n : ℕ} → {Γ : Context} → {T : valU n Γ} → (e : UnApplicable {n} Γ T) → (P e)
indu P i a (InCtx {n} {Γ} {T}) = i {n} {Γ} {T}
indu P i a (App f x) = a f x

-- now, time to tie the knot and make Exp fully defined.
Value' = Value -- TODO: might help when defining ind later to move the up?
valU n Γ = Value Γ (U' n)
U' n {∅} = U n
U' n {ConsCtx {m} Γ T} = WeakenType {suc n} {m} {Γ} {T} (U' n {Γ})
Pi' = Pi
WeakenType = Weaken
-- what all of this has created is:
-- Exp : {n : ℕ} → (Γ : Context) → Exp Γ (U n) → Set
-- U : (n : ℕ) → ∀ {Γ} → Exp Γ (U (suc n))

-- Now, I will define EVALUTION!!!!! in the form of: substitution.
-- This can be used to define other stuff, like general Application

substType e x = {!   !}
