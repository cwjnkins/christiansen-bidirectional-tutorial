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

unroll : Ty → Ty
unroll τ = go-unroll (un-μ τ) 0
  where
  go-unroll : Ty → Nat → Ty
  go-unroll bool n = bool
  go-unroll (τ₁ ⟶ τ₂) n = (go-unroll τ₁ n) ⟶ (go-unroll τ₂ n)
  go-unroll (eith τ₁ τ₂) n = eith (go-unroll τ₁ n) (go-unroll τ₂ n)
  go-unroll (prod τ₁ τ₂) n = prod (go-unroll τ₁ n) (go-unroll τ₂ n)
  go-unroll (μ τ₁) n = μ (go-unroll τ₁ (suc n))
  go-unroll (tv x) n with compare x n
  ... | less lt = tv x
  ... | equal eq = tag 0 τ
  ... | greater (diff k eq) = tv (k + n) -- this is actually nonsense, right?
  go-unroll (tag x τ₁) n = tag (suc x) (go-unroll τ₁ n)

private
  test₂-list :
    unroll test₁-list
    ≡ (eith bool $
       prod bool $
       tag 0 $ μ eith bool (prod bool $ tv 0))
  test₂-list = refl

roll : Ty → Ty
roll τ = μ (go-roll τ 0)
  where
  go-roll : Ty → Nat → Ty
  go-roll bool n = bool
  go-roll (τ₁ ⟶ τ₂) n = go-roll τ₁ n ⟶ go-roll τ₂ n
  go-roll (eith τ₁ τ₂) n = eith (go-roll τ₁ n) (go-roll τ₂ n)
  go-roll (prod τ₁ τ₂) n = prod (go-roll τ₁ n) (go-roll τ₂ n)
  go-roll (μ τ₁) n
    = μ (go-roll τ₁ (suc n))
  go-roll (tv x) n = tv x
  go-roll (tag x τ₁) n with compare x n
  ... | less lt = tag x τ₁
  ... | equal eq = tv n
  ... | greater (diff k eq) = tag (k + n) τ₁

private
  test₃-list : roll (unroll test₁-list) ≡ test₁-list
  test₃-list = refl

postulate
  iso-rec : ∀ τ → μ τ ≡ roll (unroll (μ τ))
