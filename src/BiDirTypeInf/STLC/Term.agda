module BiDirTypeInf.STLC.Term where

open import Prelude
open import Container.List

infixr 0 _⟶_
data Ty : Set where
  bool : Ty
  _⟶_  : (σ τ : Ty) → Ty

private
  showTy : Ty → String
  showTy bool
    = "bool"
  showTy (σ ⟶ τ)
    = "(" <> showTy σ <> " -> " <> showTy τ <> ")"

  eqTy : (τ σ : Ty) → Dec (τ ≡ σ)
  eqTy bool bool = yes refl
  eqTy bool (σ ⟶ σ₁) = no (λ ())
  eqTy (τ ⟶ τ₁) bool = no (λ ())
  eqTy (τ ⟶ τ₁) (σ ⟶ σ₁)
    with eqTy τ σ
  ... | no  ne
    = no (λ { refl → ne refl})
  ... | yes refl
    with eqTy τ₁ σ₁
  ... | (no ne)
    = no (λ { refl → ne refl})
  ... | (yes refl)
    = yes refl

data Raw : Set where
  var : Nat → Raw
  app : (s t : Raw) → Raw
  lam : Nat → Raw → Raw
  if  : (c t e : Raw) → Raw
  tru fls : Raw
  ann : Ty → Raw → Raw

private
  showRaw : Raw → String
  showRaw (var x)
    = "$" <> show x
  showRaw (app s t)
    = "(" <> showRaw s <> " @ " <> showRaw t <> ")"
  showRaw (lam x r)
    = "(\\" <> show x <> " . " <> showRaw r <> ")"
  showRaw (if c t e)
    = "(if " <> showRaw c <> " then " <> showRaw t <> " else " <> showRaw e <> ")"
  showRaw tru
    = "tru"
  showRaw fls
    = "fls"
  showRaw (ann τ r)
    = "(" <> showRaw r <> " : " <> showTy τ <> ")"

instance
  ShowTy : Show Ty
  ShowTy = simpleShowInstance showTy

  EqTy : Eq Ty
  EqTy = record { _==_ = eqTy }

  ShowRaw : Show Raw
  ShowRaw = simpleShowInstance showRaw

data TCMode : Set where
  chk inf : TCMode

Cxt = List Ty

data Term (Γ : Cxt) : TCMode → Ty → Set where
  var : ∀ {τ}
        → τ ∈ Γ
        --------------
        → Term Γ inf τ
  app : ∀ {σ τ}
        → Term Γ inf (σ ⟶ τ) → Term Γ chk σ
        -----------------------------------
        → Term Γ inf τ
  lam : ∀ {σ τ}
        → Term (σ ∷ Γ) chk τ
        --------------------
        → Term Γ chk (σ ⟶ τ)
  if  : ∀ {τ}
        → Term Γ chk bool → Term Γ chk τ → Term Γ chk τ
        -----------------------------------------------
        → Term Γ chk τ
  tru fls :
        --------------
        Term Γ inf bool
  ann : ∀ τ
        → Term Γ chk τ
        --------------
        → Term Γ inf τ
  chkinf : ∀ {τ}
        → Term Γ inf τ
        --------------
        → Term Γ chk τ

eraseTerm : ∀ {Γ m τ} → Term Γ m τ → Raw
eraseTerm (var x)
  = var (forgetAny x)
eraseTerm (app s t)
  = app (eraseTerm s) (eraseTerm t)
eraseTerm {Γ} (lam t)
  = lam (length Γ ) (eraseTerm t)
eraseTerm (if c t e)
  = if (eraseTerm c) (eraseTerm t) (eraseTerm e)
eraseTerm tru
  = tru
eraseTerm fls
  = fls
eraseTerm (ann τ t)
  = ann τ (eraseTerm t)
eraseTerm (chkinf t)
  = eraseTerm t
