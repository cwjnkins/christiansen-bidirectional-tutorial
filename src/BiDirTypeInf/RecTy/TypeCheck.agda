module BiDirTypeInf.RecTy.TypeCheck where

open import Prelude
open import Container.List

open import BiDirTypeInf.RecTy.Ty
open import BiDirTypeInf.RecTy.Term

data TCMode : Set where
  chk inf : TCMode

Cxt = List Ty

data Term (Γ : Cxt) : TCMode → Ty → Set where
  var : ∀ {τ}
        → τ ∈ Γ
        -------
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
  pr : ∀ {τ σ}
       → Term Γ inf τ → Term Γ inf σ
       -----------------------------
       → Term Γ inf (prod τ σ)
  in₁ : ∀ {τ σ}
        → Term Γ chk τ
        ----------------------------
        → Term Γ chk (eith τ σ)
  in₂ : ∀ {τ σ}
        → Term Γ chk σ
        --------------
        → Term Γ chk (eith τ σ)
  unrll : ∀ {τ}
        → Term Γ inf τ
        --------------
        → Term Γ inf (unroll τ)
  rll : ∀ α
      → Term Γ chk (unroll α)
      --------------
      → Term Γ inf α
  ann : ∀ τ
        → Term Γ chk τ
        --------------
        → Term Γ inf τ
  chkinf : ∀ {τ}
        → Term Γ inf τ
        --------------
        → Term Γ chk τ

private
  list : Ty
  list = μ (eith bool (prod bool (tv 0)))

  test₁-list : Term [] inf list
  test₁-list = rll list (in₁ (chkinf tru))

  test₂-list : Term [] inf list
  test₂-list = rll list (in₂ (chkinf (pr tru test₁-list)))
