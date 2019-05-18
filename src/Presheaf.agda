open import Level
open import Relation.Binary hiding (_⇒_)

module Presheaf (P : Preorder zero zero zero) where

open import Type P

data _⊆_ : Ctx → Ctx → Set where
  base : Ø ⊆ Ø
  keep : ∀ {T Γ Δ} → Γ ⊆ Δ → (Γ `, T) ⊆ (Δ `, T)
  drop : ∀ {T Γ Δ} → Γ ⊆ Δ → (Γ `, T) ⊆ Δ

⊆-refl : Reflexive _⊆_
⊆-refl {Ø}      = base
⊆-refl {Γ `, T} = keep ⊆-refl

⊆-trans : Transitive _⊆_
⊆-trans base q = q
⊆-trans (keep p) (keep q) = keep (⊆-trans p q)
⊆-trans (keep p) (drop q) = drop (⊆-trans p q)
⊆-trans (drop p) q        = drop (⊆-trans p q)

record 𝒫 : Set₁ where
  field
    In   : Ctx → Set
    Wken : ∀ {Δ Γ} (Γ⊆Δ : Γ ⊆ Δ) → (In Δ → In Γ)


open 𝒫

-- natural transformations
_→'_ : (P Q : 𝒫) → Set
_→'_ P Q = ∀ {Γ} → (P .In Γ → Q .In Γ)


open import Data.Unit
open import Data.Product
  using (_×_ ; proj₁ ; proj₂ ; _,_ ; Σ)

_⇒'_ : 𝒫 → 𝒫 → 𝒫
(P ⇒' Q) .In Γ        = ∀ {Δ} → Δ ⊆ Γ → P .In Δ → Q .In Δ
(P ⇒' Q) .Wken τ f τ' = f (⊆-trans τ' τ)

_×'_ : 𝒫 → 𝒫 → 𝒫
In (P ×' Q) Γ = (In P Γ) × (In Q Γ)
Wken (P ×' Q) Γ⊆Δ (fst , snd) = (Wken P Γ⊆Δ fst) , (Wken Q Γ⊆Δ snd)

𝟙' : 𝒫
𝟙' = record { In = λ _ → ⊤ ; Wken = λ Γ⊆Δ _ → tt }
