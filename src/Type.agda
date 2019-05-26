open import Relation.Binary
  hiding (_⇒_)
open import Level
open import Relation.Binary.PropositionalEquality using (_≡_)

open Preorder

module Type
  (P : Preorder zero zero zero)
  (L : Preorder zero zero zero)
  where

-- the index set
I : Set
I = Carrier P

-- set of labels
Label : Set
Label = Carrier L

_≼_     = _∼_ P
≼-refl  = refl P
≼-trans = trans P

infixr 10 _⇒_

data Type  : Set where
  𝕓    : (i : I)      → Type
  _⇒_  : (a b : Type) → Type
  ⟨_⟩_ : Type → Label → Type

data _⊲_ : Type → Type → Set where
  ⊲-refl : ∀ {a}       → a ⊲ a
  -- ⊲-T    : ∀ {ℓ} {a b} → a ⊲ b → a ⊲ (⟨ b ⟩ ℓ )
  ⊲-⇒l   : ∀ {a b c}   → a ⊲ b → a ⊲ (b ⇒ c)
  ⊲-⇒r   : ∀ {a b c}   → a ⊲ b → a ⊲ (c ⇒ b)


data Ctx : Set where
  Ø    : Ctx
  _`,_ : Ctx → Type → Ctx

data _⊲C_ : Type → Ctx → Set where
  ze : ∀ {Γ} {a b} → a ⊲ b  → a ⊲C (Γ `, b)
  su : ∀ {Γ} {a b} → a ⊲C Γ → a ⊲C (Γ `, b)

