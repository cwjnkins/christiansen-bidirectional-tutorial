module BiDirTypeInf.Container.List where

open import Prelude
open import Tactic.Nat

open import Container.List public

module _ {a} {A : Set a} where

  data Index∈ (xs : List A) : Nat → Set a where
    found : ∀ {x} → (x∈xs : x ∈ xs) → Index∈ xs (forgetAny x∈xs)
    bad   : ∀ {m} n → m ≡ length xs + n → Index∈ xs m

  index∈ : (xs : List A) → (n : Nat) → Index∈ xs n
  index∈ [] n
    = bad n refl
  index∈ (x ∷ xs) zero
    = found (zero refl)
  index∈ (x ∷ xs) (suc n)
    with index∈ xs n
  ... | bad n' eq = bad n' (by eq)
  ... | found x∈xs = found (suc x∈xs)
