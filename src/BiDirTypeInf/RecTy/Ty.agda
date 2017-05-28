module BiDirTypeInf.RecTy.Ty where

open import Prelude
open import Prelude.Equality.Unsafe
open import Tactic.Nat

data Ty : Set where
  bool : Ty
  _⟶_ eith prod
       : (σ τ : Ty) → Ty
  μ_   : Ty → Ty
  tv   : Nat → Ty
  tag  : Nat → Ty → Ty

leftTy : Ty → Ty
leftTy (σ ⟶ τ) = σ
leftTy (eith σ τ) = σ
leftTy (prod σ τ) = σ
leftTy τ = τ

rightTy : Ty → Ty
rightTy (σ ⟶ τ) = τ
rightTy (eith σ τ) = τ
rightTy (prod σ τ) = τ
rightTy τ = τ

private
  eqTy : ∀ (τ₁ τ₂ : Ty) → Dec (τ₁ ≡ τ₂)
  eqTy bool bool
    = yes refl
  eqTy (σ₁ ⟶ τ₁) (σ₂ ⟶ τ₂)
    with eqTy σ₁ σ₂ | eqTy τ₁ τ₂
  ... | no neq | _
    = no (λ { refl → neq refl})
  ... | yes eq | (no neq)
    = no (λ { refl → neq refl})
  ... | yes refl | (yes refl)
    = yes refl
  eqTy (eith σ₁ τ₁) (eith σ₂ τ₂)
    with eqTy σ₁ σ₂ | eqTy τ₁ τ₂
  ... | no neq | _
    = no (λ { refl → neq refl})
  ... | yes eq | (no neq)
    = no (λ { refl → neq refl})
  ... | yes refl | (yes refl)
    = yes refl
  eqTy (prod σ₁ τ₁) (prod σ₂ τ₂)
    with eqTy σ₁ σ₂ | eqTy τ₁ τ₂
  ... | no neq | _
    = no (λ { refl → neq refl})
  ... | yes eq | (no neq)
    = no (λ { refl → neq refl})
  ... | yes refl | (yes refl)
    = yes refl
  eqTy (μ τ₁) (μ τ₂)
    with eqTy τ₁ τ₂
  ... | no neq
    = no (λ { refl → neq refl})
  ... | yes refl
    = yes refl
  eqTy (tv x) (tv y)
    with x == y
  ... | no neq
    = no (λ { refl → neq refl})
  ... | yes refl
    = yes refl
  eqTy (tag x τ) (tag y σ)
    with x == y | eqTy σ τ
  ... | no neq   | _
    = no (λ { refl → neq refl})
  ... | yes eq   | (no neq)
    = no (λ { refl → neq refl})
  ... | yes refl | (yes refl)
    = yes refl
  eqTy _      _
    = no unsafeNotEqual

instance
  EqTy : Eq Ty
  EqTy = record { _==_ = eqTy }

postulate
  instance
    ShowTy : Show Ty

private
  test₁-list : Ty
  test₁-list = μ (eith bool (prod bool (tv 0)))

un-μ : Ty → Ty
un-μ (μ τ) = τ
un-μ τ     = τ

private
  unroll-helper : (τ τ' : Ty) → Nat → Ty
  unroll-helper τ bool n = bool
  unroll-helper τ (τ₁ ⟶ τ₂) n = (unroll-helper τ τ₁ n) ⟶ (unroll-helper τ τ₂ n)
  unroll-helper τ (eith τ₁ τ₂) n = eith (unroll-helper τ τ₁ n) (unroll-helper τ τ₂ n)
  unroll-helper τ (prod τ₁ τ₂) n = prod (unroll-helper τ τ₁ n) (unroll-helper τ τ₂ n)
  unroll-helper τ (μ τ₁) n = μ (unroll-helper τ τ₁ (suc n))
  unroll-helper τ (tv x) n with compare x n
  ... | less lt = tv x
  ... | equal eq = tag 0 τ
  ... | greater (diff k eq) = tv (k + n) -- this is actually nonsense, right?
  unroll-helper τ (tag x τ₁) n = tag (suc x) (unroll-helper τ τ₁ n)

  roll-helper : Ty → Nat → Ty
  roll-helper bool n = bool
  roll-helper (τ₁ ⟶ τ₂) n = roll-helper τ₁ n ⟶ roll-helper τ₂ n
  roll-helper (eith τ₁ τ₂) n = eith (roll-helper τ₁ n) (roll-helper τ₂ n)
  roll-helper (prod τ₁ τ₂) n = prod (roll-helper τ₁ n) (roll-helper τ₂ n)
  roll-helper (μ τ₁) n
    = μ (roll-helper τ₁ (suc n))
  roll-helper (tv x) n = tv x
  roll-helper (tag x τ₁) n with compare x n
  ... | less lt = tag x τ₁
  ... | equal eq = tv n
  ... | greater (diff k eq) = tag (k + n) τ₁


unroll : Ty → Ty
unroll τ = unroll-helper τ (un-μ τ) 0

private
  test₂-list :
    unroll test₁-list
    ≡ (eith bool $
       prod bool $
       tag 0 $ μ eith bool (prod bool $ tv 0))
  test₂-list = refl

roll : Ty → Ty
roll τ = μ (roll-helper τ 0)

private
  test₃-list : roll (unroll test₁-list) ≡ test₁-list
  test₃-list = refl

postulate
  iso-rec : ∀ τ → μ τ ≡ roll (unroll (μ τ))
-- iso-rec : ∀ τ → μ τ ≡ roll (unroll (μ τ))
-- iso-rec bool = refl
-- iso-rec (τ ⟶ τ₁) = {!!}
-- iso-rec (eith τ τ₁) = {!!}
-- iso-rec (prod τ τ₁) = {!!}
-- iso-rec (μ τ) = {!!}
-- iso-rec (tv x) = {!!}
-- iso-rec (tag x τ) = {!!}
