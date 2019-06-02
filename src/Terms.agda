{-# OPTIONS --postfix-projections #-}

open import Level using (zero; suc; _⊔_)
open import Algebra.Ordered using (Promonoid)
import Data.List.Relation.Unary.Any       as ListAny
import Data.List.Membership.Propositional as ListMembership
open import Function using (_∘_; flip)
open import Relation.Binary using (Preorder)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

-- The syntax of intrinsically typed terms are parametrized by
--
--  * a preordered set of base types,
--  * a promonoid of effects.

module Terms {c ℓ₁ ℓ₂}
             (Base    : Preorder c ℓ₁ ℓ₂)
             (Effects : Promonoid c ℓ₁ ℓ₂)
             where

open import Types      Base Effects
open import Coercions  Base Effects
open import Presheaves Base Effects

open PSh

-- Variables/deBrujin indexes are positions in contexts

open ListMembership public using (_∈_)
open ListAny        public using (here; there)

-- Weakening of variables

weakenVar : ∀ {a} {Γ Δ} → Γ ⊆ Δ → a ∈ Δ → a ∈ Γ
weakenVar Φ = lookup (flip PropEq.trans) Φ

-- Variables of a given type form a presheaf

Var : Tp → PSh c
(Var a) .on Γ   = a ∈ Γ
(Var a) .weaken = weakenVar

infixr 8 _·_ _*_
infix  4 _⊢_
infixr 4 _,_
infixr 2 _∋_

-- The syntax of intrinsically typed terms

data _⊢_ (Γ : Ctx) : Tp → Set (c ⊔ ℓ₂) where

  var : ∀ {a}
      → a ∈ Γ
        ----- (variable lookup)
      → Γ ⊢ a

  ⟨⟩ : --------- (unit element)
       Γ ⊢ unit
 
  _,_ : ∀ {a b}
      → Γ ⊢ a
      → Γ ⊢ b
        --------- (pairing)
      → Γ ⊢ a 𝕩 b
 
  fst : ∀ {a b}
      → Γ ⊢ a 𝕩 b
        --------- (first projection)
      → Γ ⊢ a

  snd : ∀ {a b}
      → Γ ⊢ a 𝕩 b
        --------- (second projection)
      → Γ ⊢ b

  ƛ : ∀ {a b}
    → a ∷ Γ ⊢ b
      --------- (abstraction)
    → Γ ⊢ a ⇒ b
 
  _·_ : ∀ {a b}
      → Γ ⊢ a ⇒ b
      → Γ ⊢ a
        --------- (application)
      → Γ ⊢ b

  ◇ : ∀ {a}
    → Γ ⊢ a
      ----------- (monadic unit/return/diamond)
    → Γ ⊢ ⟨ ε ⟩ a

  _>>=_ : ∀ {e f a b}
        → Γ ⊢ ⟨ e ⟩ a
        → a ∷ Γ ⊢ ⟨ f ⟩ b
          --------------- (monadic bind/Kleisli extension)
        → Γ ⊢ ⟨ e ∙ f ⟩ b
 
  _*_ : ∀ {a b}
      → a <: b
      → Γ ⊢ a
        ------ (subsumption)
      → Γ ⊢ b

  _∋_ : ∀ a
      → Γ ⊢ a
        ----- (ascription)
      → Γ ⊢ a

-- An admissible rule: computation coercion

⊢-up : ∀ {Γ e f a}
     → e ⊑ f
     → Γ ⊢ ⟨ e ⟩ a
       ----------- (computation coercion)
     → Γ ⊢ ⟨ f ⟩ a
⊢-up φ t = ⟨ φ ⟩ refl * t


-- Weakening of terms

weakenTerm : ∀ {a} {Γ Δ} → Γ ⊆ Δ → Δ ⊢ a → Γ ⊢ a
weakenTerm Φ ⟨⟩        = ⟨⟩
weakenTerm Φ (t , u)   = weakenTerm Φ t , weakenTerm Φ u
weakenTerm Φ (fst t)   = fst (weakenTerm Φ t)
weakenTerm Φ (snd t)   = snd (weakenTerm Φ t)
weakenTerm Φ (ƛ t)     = ƛ (weakenTerm (refl ∷ Φ) t)
weakenTerm Φ (var x)   = var (weakenVar Φ x)
weakenTerm Φ (t · u)   = weakenTerm Φ t · weakenTerm Φ u
weakenTerm Φ (◇ t)     = ◇ (weakenTerm Φ t)
weakenTerm Φ (t >>= u) = weakenTerm Φ t >>= weakenTerm (refl ∷ Φ) u
weakenTerm Φ (α * t)   = α * (weakenTerm Φ t)
weakenTerm Φ (a ∋ t)   = a ∋ (weakenTerm Φ t)

-- Terms of a given type form a presheaf

Term : Tp → PSh (c ⊔ ℓ₂)
(Term a) .on Γ   = Γ ⊢ a
(Term a) .weaken = weakenTerm
