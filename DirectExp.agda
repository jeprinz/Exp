open import Data.Nat

mutual
  Context' : Set
  expU : (n : ℕ) → (Γ : Context') → Set
  -- expU {n} Γ = Exp {n} Γ (U (suc n))

  data Context : Set where
    ∅ : Context
    ConsCtx : ∀ {n} → (Γ : Context') → expU n Γ → Context
  Context' = Context


  U' : (n : ℕ) → ∀ {Γ} → expU n Γ
  data Exp : {n : ℕ} → (Γ : Context') → expU n Γ → Set where
    U : (n : ℕ) → ∀ {Γ} → Exp Γ (U' n)

    -- InCtx : ∀ {Γ} → (T : expU Γ) → Exp (ConsCtx Γ T) {!   !} -- <-- here is where type needs InCtx.
    -- WeakerCtx : ∀ {n} → ∀ {Γ} → ∀ {T A} → Exp {n} Γ A → Exp {n} (ConsCtx Γ T) (WeakerCtx A)

    -- Lambda : ∀ {n} → ∀ {Γ} → ∀ {A} → ∀ {B} → Exp {n} (ConsCtx Γ A) B → Exp Γ (Pi {n} A B)
    -- App : ∀ {n} → ∀ {Γ} → ∀ {A} → ∀ {B} → Exp {n} Γ (Pi {n} A B) → (x : Exp Γ A) →
      -- Exp Γ ({!   !}) -- In the hole, put the substitution of x in B

  expU n Γ = Exp {n} Γ (U' n)
  U' = U
