{-The intent of this file is to test a different approach to the Exp type which
doesn't reference Agda types at all.  If possible, this should make pattern
matching on Exp values easier because its not possible to pattern match types.-}

-- open import Agda.Primitive -- Level
open import Data.Nat

mutual
  data Context : {n : ℕ} → Set where
    ∅ : ∀ {n} → Context {n}
    ConsCtx : ∀ {n} → (Γ : Context {n}) → Type {n} Γ → Context {n}

  -- ctxType : {n : ℕ} → Context {n} → Set
  -- ctxType = {!   !}


  data Type : {n : ℕ} → Context {n} → Set where --elements of Uₙ
    U : (n : ℕ) → ∀ {Γ} → Type {suc n} Γ
    Pi : ∀ {n} → ∀ {Γ} → (A : Type Γ) → (B : Type (ConsCtx Γ A)) → Type {n} Γ
    fromExp : ∀ {n} → ∀ {Γ} → Exp {suc n} ? (U n) → Type {n} Γ
    InCtx : ∀ {n} → ∀ {Γ} → Type {n} (ConsCtx Γ (U n))
    WeakerCtx : ∀ {n} → ∀ {Γ} → ∀ {T} → Type {n} Γ → Type {n} (ConsCtx Γ T)

-- should be Type (ConsCtx ∅ U), which essentially does "InCtx"

  data Exp : {n : ℕ} → (Γ : Context {n}) → Type {n} Γ → Set where
    fromType : ∀ {n} → ∀ {Γ} → Type {n} Γ → Exp {suc n} (liftCtx n Γ) (U (suc n))
    InCtx : ∀ {n} → ∀ {Γ} → (T : Type {n} Γ) → Exp {n} (ConsCtx Γ T) (WeakerCtx T) -- <-- here is where type needs InCtx.
    WeakerCtx : ∀ {n} → ∀ {Γ} → ∀ {T A} → Exp {n} Γ A → Exp {n} (ConsCtx Γ T) (WeakerCtx A)

    Lambda : ∀ {n} → ∀ {Γ} → ∀ {A} → ∀ {B} → Exp {n} (ConsCtx Γ A) B → Exp Γ (Pi {n} A B)
    App : ∀ {n} → ∀ {Γ} → ∀ {A} → ∀ {B} → Exp {n} Γ (Pi {n} A B) → (x : Exp Γ A) →
      Exp Γ ({!   !}) -- In the hole, put the substitution of x in B

    -- App : {Γ : Context} → {A : ctxType Γ → Set (ll n)} → {B : (γ : ctxType Γ) → A γ → Set (ll n)} →
      -- Exp Γ (λ γ → (a : A γ) → B γ a) → (x : Exp Γ A) → Exp Γ (λ γ → B γ (eval γ x))


  liftCtx : (n : ℕ) → Context {n} → Context {suc n}
  liftCtx n ∅ = ∅
  liftCtx n (ConsCtx Γ T) = ConsCtx (liftCtx n Γ) (liftType n T)

  liftType : (n : ℕ) → ∀ {Γ} → Type {n} Γ → Type {suc n} (liftCtx n Γ)
  liftType n T = fromExp (fromType T)

mutual -- TODO: subst can't be in mutual block , but substt can???? but it needs to depend on subst...
  substt : ∀ {n} → ∀ {Γ} → {T : Type Γ} →
    Type {n} (ConsCtx Γ T) → (x : Exp {n} Γ T) → Type {n} Γ
  substt (U n) x = U n
  substt (Pi T T₁) x = {!   !}
  substt {n} {Γ} {T} (fromExp .{n} .{ConsCtx Γ T} x₁) x = fromExp {n} {Γ} (subst {n} {Γ} {T} {U n {ConsCtx Γ T}} x₁ x)
  substt InCtx x = fromExp x
  substt (WeakerCtx T) x = T

  subst : ∀ {n} → ∀ {Γ} → {T : Type Γ} → {A : Type (ConsCtx Γ T)} →
    Exp {n} (ConsCtx Γ T) A → (x : Exp {n} Γ T) → Exp {n} Γ {!   !}
  subst = {!   !}
