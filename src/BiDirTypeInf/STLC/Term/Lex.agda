module BiDirTypeInf.STLC.Term.Lex where

open import Prelude
open import Text.Lex

data Token : Set where
  t: : Token       -- annotation
  tb t⟶ : Token    -- types
  t$ : Token       -- var
  tn : Nat → Token -- var
  ta : Token       -- app
  tt tf : Token    -- tru fls
  t[ t] : Token    -- parens
  tλ tp : Token    -- lambda
  ti th te : Token -- if

tn-inj : ∀ {m n} → tn m ≡ tn n → m ≡ n
tn-inj refl = refl

private
  open import Prelude.Equality.Unsafe

  eqToken : (x y : Token) → Dec (x ≡ y)
  eqToken t: t: = yes refl
  eqToken tb tb = yes refl
  eqToken t⟶ t⟶ = yes refl
  eqToken t$ t$ = yes refl
  eqToken (tn m) (tn n)
    with m == n
  ... | no neq  = no (λ eq → neq (tn-inj eq))
  ... | yes refl
                = yes refl
  eqToken ta ta = yes refl
  eqToken tt tt = yes refl
  eqToken tf tf = yes refl
  eqToken t[ t[ = yes refl
  eqToken t] t] = yes refl
  eqToken tλ tλ = yes refl
  eqToken tp tp = yes refl
  eqToken ti ti = yes refl
  eqToken th th = yes refl
  eqToken te te = yes refl
  eqToken x  y  = no unsafeNotEqual
  
instance
  EqToken : Eq Token
  EqToken = record { _==_ = eqToken }

keywordTok : Token → String → TokenDFA Char (Maybe Token)
keywordTok t k = just t <$ keywordToken (unpackString k)

tokenSpecs : List (TokenDFA Char (Maybe Token))
tokenSpecs
  = keywordTok t: ":"
    ∷ keywordTok tb "bool"
    ∷ keywordTok t⟶ "->"
    ∷ keywordTok t$ "$"
    ∷ (just ∘ tn <$> natToken)
    ∷ keywordTok ta "@"
    ∷ keywordTok tt "tru"
    ∷ keywordTok tf "fls"
    ∷ keywordTok t[ "("
    ∷ keywordTok t] ")"
    ∷ keywordTok tλ "\\"
    ∷ keywordTok tp "."
    ∷ keywordTok ti "if"
    ∷ keywordTok th "then"
    ∷ keywordTok te "else"
    ∷ (nothing <$ matchToken isSpace)
    ∷ []

lex : String → List Token
lex s = concatMap (maybe [] [_]) ∘ tokenize tokenSpecs ∘ unpackString $ s

private
  test₁-data : String
  test₁-data = "(\\ 0 . if $0 then fls else tru) : bool -> bool"

  test₁ : List Token
  test₁ = lex test₁-data
