open import Algebra.Ordered using (Promonoid)
open import Data.List using (List)
open import Relation.Binary using (Preorder)

-- The syntax of types is parametrized by
--
--  * a preordered set of base types,
--  * a promonoid of effects.

module Types {c ℓ₁ ℓ₂}
             (Base    : Preorder c ℓ₁ ℓ₂)
             (Effects : Promonoid c ℓ₁ ℓ₂)
             where

-- Shorthands for easier access to the preorders

module Bs  = Preorder  Base
module Eff = Promonoid Effects

open Bs  public using ()       renaming (Carrier to Bs;  _∼_ to _≤_)
open Eff public using (ε; _∙_) renaming (Carrier to Eff; _∼_ to _⊑_)

infixr 7 _⇒_
infixl 8 _𝕩_
infixr 9 ⟨_⟩_

-- The syntax of simple types

data Tp : Set c where
  bs   : (i : Bs)           → Tp   -- base types
  unit :                      Tp   -- unit type
  _𝕩_  : (a b : Tp)         → Tp   -- product type
  _⇒_  : (a b : Tp)         → Tp   -- function type
  ⟨_⟩_ : (e : Eff) (a : Tp) → Tp   -- graded monad


-- Contexts are just ordered sequences of types.

Ctx : Set c
Ctx = List Tp

open List public using ([]; _∷_)
