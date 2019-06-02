open import Level using (_⊔_)
open import Algebra.Ordered using (Promonoid)
import Data.List.Relation.Binary.Sublist.Setoid as Sublist
open import Relation.Binary using (Preorder)
import Relation.Binary.PropositionalEquality as PropEq

-- Subtyping coercions are parametrized by
--
--  * a preordered set of base types,
--  * a preordered monoid of effects.
--
-- These two preorders generate the subtyping relation.

module Coercions {c ℓ₁ ℓ₂}
                 (Base    : Preorder c ℓ₁ ℓ₂)
                 (Effects : Promonoid c ℓ₁ ℓ₂)
                 where

open import Types Base Effects

infix 4 _<:_ _≪:_

-- Declarative subtyping is a binary relation over types.
--
-- Alternative interpretation: the intrinsically typed syntax of
-- subtyping coercions `α : a <: b` between types `a` and `b`.

data _<:_ : Tp → Tp → Set (c ⊔ ℓ₂) where

  coe : ∀ {i j}
      → i ≤ j
        ------------
      → bs i <: bs j

         ------------
  unit : unit <: unit


  _⇒_ : ∀ {a₁ a₂ b₁ b₂}
      → a₂ <: a₁
      → b₁ <: b₂
        ------------------
      → a₁ ⇒ b₁ <: a₂ ⇒ b₂
 
  _𝕩_ : ∀ {a₁ a₂ b₁ b₂}
      → a₁ <: a₂
      → b₁ <: b₂
        ------------------
      → a₁ 𝕩 b₁ <: a₂ 𝕩 b₂

  ⟨_⟩_ : ∀ {e₁ e₂ a₁ a₂}
       → e₁ ⊑ e₂
       → a₁ <: a₂
         ----------------------
       → ⟨ e₁ ⟩ a₁ <: ⟨ e₂ ⟩ a₂

  refl : ∀ {a}
         ------
       → a <: a

  trans : ∀ {a₁ a₂ a₃}
        → a₁ <: a₂
        → a₂ <: a₃
          --------
        → a₁ <: a₃


-- Two notions of context morphism, one allowing only weakening, the
-- other including subtyping.

-- Order Preserving Embeddings (OPEs)
--
-- NOTE: we are reusing support for sublists from the standard library
-- to implement OPEs here, but change the direction of the relation to
-- adopt the usual order on contexts: given contexts Γ and Δ
--
--   Γ ⊆ Δ   iff   everything that can be typed in Δ can be typed in Γ
-- 
-- This also ensures that our terminology stays consistent with the
-- usual interpretation of presheafs as contravariant functors.

open Sublist (PropEq.setoid Tp) public renaming
  ( _⊆_ to _⊇_    -- OPEs are the inverse of the sublist relation

  -- Constructors/rules
  ; _∷ʳ_ to _∷ˡ_  -- weakening (dropping a variable on the left)

  -- Order-theoretic properties

  ; ⊆-refl  to ⊇-refl   -- reflexivity
  ; ⊆-trans to ⊇-trans  -- transitivity
  )

  using
 
  -- Constructors/rules

  ( []   -- empty contexts are related
  ; _∷_  -- context extensions are related

  -- Generalized lookup
  ; lookup
  )

-- OPEs are the inverse of the sublist relation

_⊆_ : Ctx → Ctx → Set c
Γ ⊆ Δ = Δ ⊇ Γ

⊆-refl : ∀ {Γ} → Γ ⊆ Γ
⊆-refl = ⊇-refl

⊆-trans : ∀ {Γ Δ E} → Γ ⊆ Δ → Δ ⊆ E → Γ ⊆ E
⊆-trans Φ Ψ = ⊇-trans Ψ Φ

-- Subtyping lifted pointwise to context, combined with OPEs
--
-- Alternative interpretation: the intrinsically typed syntax of
-- context morphisms `Φ : Γ ≪: Δ` between contexts `Γ` and `Δ`.
--
-- FIXME: is this ever used?

data _≪:_ : Ctx → Ctx → Set (c ⊔ ℓ₂) where

       ---------
  [] : [] ≪: []
  
  _∷_ : ∀ {a b Γ Δ}
      → a <: b
      → Γ ≪: Δ
        ---------------
      → a ∷ Γ ≪: b ∷ Δ

  _∷ˡ_ : ∀ a {Γ Δ}
       → Γ ≪: Δ
         -----------
       → a ∷ Γ ≪: Δ
