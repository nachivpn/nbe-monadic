open import Relation.Binary
  hiding (_⇒_)
open import Level
open import Relation.Binary.PropositionalEquality using (_≡_)

open Preorder

module Type (P : Preorder zero zero zero) where

-- the index set
I : Set
I = Carrier P

_≼_     = _∼_ P
≼-refl  = refl P
≼-trans = trans P

infixr 10 _⇒_

data Type  : Set where
  𝕓   : (i : I)      → Type
  _⇒_ : (a b : Type) → Type
  𝕋   : Type         → Type

data Ctx : Set where
  Ø    : Ctx
  _`,_ : Ctx → Type → Ctx



