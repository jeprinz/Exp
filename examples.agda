open import exp

--testing it out a little:
e : Exp ∅ (Pi (U' 0) (U' 0)) -- Type → Type
e = Lambda InCtx -- λ x . x

e' : Exp ∅ (Pi (U' 1) (U' 1)) -- Type 1 → Type 1
e' = Lambda (U' 0) -- λ x . Type 0

polymorphicIdentity : Exp ∅ (Pi (U' 0) (Pi InCtx (Weaken InCtx))) -- (T : Type) → T → T
polymorphicIdentity = Lambda (Lambda InCtx)


-- recursor does work in practice!!!!
-- not going to be useful though without induction principle...
-- test : Exp ∅ (Pi (U' 1) (U' 1)) → ℕ
-- test e = rec (λ n → n) --U n, can't happen
--              (2) -- InCtx, note this can't even happen
--              (λ e → rec {!   !} {!   !} {!   !} {!   !} {!   !} {!   !} e) -- Weaken e, also can't happen
--              (λ A B → rec {!   !} {!   !} {!   !} {!   !} {!   !} {!   !} B) -- Pi A B, also can't happen
--              (λ e → rec {!   !} {!   !} {!   !} {!   !} {!   !} {!   !} e) -- Lambda e
--              {!   !}
--              e
