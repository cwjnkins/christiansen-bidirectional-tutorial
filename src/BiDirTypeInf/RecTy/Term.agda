module BiDirTypeInf.RecTy.Term where

open import Prelude
open import Prelude.Equality.Unsafe
open import Container.List

open import BiDirTypeInf.RecTy.Ty

data Raw : Set where
  var : Nat → Raw
  app : (s t : Raw) → Raw
  lam : Nat → Raw → Raw
  if  : (c t e : Raw) → Raw
  tru fls
      : Raw
  in₁ in₂
      : Raw → Raw
  pr  : (a b : Raw) → Raw
  pr₁ pr₂
      : Raw → Raw
  case
      : (c l r : Raw) → Raw
  unrll
      : Raw → Raw
  rll : Raw → Raw
  ann : Ty → Raw → Raw

-- TODO
private
  showRaw : Raw → String
  showRaw (var x) = "$" <> show x
  showRaw (app o r) = showRaw o <> " @ " <> showRaw r
  showRaw (lam x r) = "(fn " <> show x <> " . " <> showRaw r <> ")" 
  showRaw (if c t e) = "if " <> showRaw c <> " " <> showRaw t <> " " <> showRaw e 
  showRaw tru = "tru"
  showRaw fls = "fls"
  showRaw (in₁ r) = "in1 " <> showRaw r
  showRaw (in₂ r) = "in2 " <> showRaw r
  showRaw (pr o r) = "pr " <> showRaw o <> " " <> showRaw r 
  showRaw (pr₁ r) = "pr1 " <> showRaw r
  showRaw (pr₂ r) = "pr2 " <> showRaw r
  showRaw (case c l r) = "case " <> showRaw c <> " " <> showRaw l <> " " <> showRaw r 
  showRaw (unrll r) = "unrll " <> showRaw r
  showRaw (rll r) = "rll " <> showRaw r
  showRaw (ann x r) = "ann " <> show x <> " : " <> showRaw r

  -- eqRaw : (o r : Raw) → Dec (o ≡ r)
  -- eqRaw (var x) (var y) with x == y
  -- ... | no neq = no (λ { refl → neq refl})
  -- ... | yes refl = yes refl
  -- eqRaw (app o o') (app s s') with eqRaw o s | eqRaw o' s'
  -- ... | no neq | _ = no (λ { refl → neq refl})
  -- ... | yes eq | (no neq) = no (λ { refl → neq refl})
  -- ... | yes refl | (yes refl) = yes refl
  -- eqRaw (lam x o) r = {!!}
  -- eqRaw (if o o₁ o₂) r = {!!}
  -- eqRaw tru r = {!!}
  -- eqRaw fls r = {!!}
  -- eqRaw (in₁ o) r = {!!}
  -- eqRaw (in₂ o) r = {!!}
  -- eqRaw (pr o o₁) r = {!!}
  -- eqRaw (pr₁ o) r = {!!}
  -- eqRaw (pr₂ o) r = {!!}
  -- eqRaw (case o o₁ o₂) r = {!!}
  -- eqRaw (unrll o) r = {!!}
  -- eqRaw (rll o) r = {!!}
  -- eqRaw (ann x o) r = {!!}
  -- eqRaw o r = no unsafeNotEqual

instance
  ShowRaw : Show Raw
  ShowRaw = simpleShowInstance showRaw

  -- EqRaw   : Eq   Raw
  -- EqRaw   = record { _==_ = eqRaw }

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
  pr  : ∀ {τ σ m}
        → Term Γ m τ → Term Γ m σ
        -----------------------------
        → Term Γ m (prod τ σ)
  pr₁ : ∀ {τ σ}
        → Term Γ inf (prod τ σ)
        -----------------------
        → Term Γ inf τ
  pr₂ : ∀ {τ σ}
        → Term Γ inf (prod τ σ)
        ----------------------
        → Term Γ inf σ
  in₁ : ∀ {τ σ}
        → Term Γ chk τ
        ----------------------------
        → Term Γ chk (eith τ σ)
  in₂ : ∀ {τ σ}
        → Term Γ chk σ
        --------------
        → Term Γ chk (eith τ σ)
  case :
        ∀ {τ σ γ}
        → Term Γ inf (eith τ σ)
        → Term Γ chk (τ ⟶ γ)
        → Term Γ chk (σ ⟶ γ)
        -----------------------
        → Term Γ chk γ
  unrll : ∀ {τ}
        → Term Γ inf (roll τ)
        --------------
        → Term Γ inf τ
  rll : ∀ {τ}
        → Term Γ chk (unroll τ)
        -----------------------
        → Term Γ chk τ
  tag : ∀ {τ} n
        → Term Γ chk τ
        ------------
        → Term Γ chk (tag n τ)
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
  test₁-list = ann list (rll (in₁ (chkinf tru)))

  test₂-list : Term [] inf list
  test₂-list = ann list (rll (in₂ (pr (chkinf fls)
                                  (tag 0 (rll (in₁ (chkinf tru)))))))

  test₃-head : Term [] inf (list ⟶ bool)
  test₃-head = ann (list ⟶ bool) (lam (case {σ = rightTy (unroll list)}
                                            (unrll (var (zero refl)))
                                            (lam (chkinf (var (zero refl))))
                                            (lam (chkinf (pr₁ (var (zero refl)))))))

eraseTerm : ∀ {Γ m τ} → Term Γ m τ → Raw
eraseTerm (var x)       = var (forgetAny x)
eraseTerm (app s t)     = app (eraseTerm s) (eraseTerm t)
eraseTerm {Γ} (lam t)   = lam (length Γ) (eraseTerm t)
eraseTerm (if c t e)    = if (eraseTerm c) (eraseTerm t) (eraseTerm e)
eraseTerm tru           = tru
eraseTerm fls           = fls
eraseTerm (pr s t)      = pr (eraseTerm s) (eraseTerm t)
eraseTerm (pr₁ t)       = pr₁ (eraseTerm t)
eraseTerm (pr₂ t)       = pr₂ (eraseTerm t)
eraseTerm (in₁ t)       = in₁ (eraseTerm t)
eraseTerm (in₂ t)       = in₂ (eraseTerm t)
eraseTerm (case c l r)  = case (eraseTerm c) (eraseTerm l) (eraseTerm r)
eraseTerm (unrll t)     = unrll (eraseTerm t)
eraseTerm (rll t)       = rll (eraseTerm t)
eraseTerm (ann τ t)     = ann τ (eraseTerm t)
eraseTerm (chkinf t)    = eraseTerm t
eraseTerm (tag n t)     = eraseTerm t
