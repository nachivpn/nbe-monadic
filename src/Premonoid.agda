module Premonoid where

  open import Relation.Binary
  open import Level using (zero) 
  open import Relation.Binary.PropositionalEquality
  open Preorder
  
  record Monoid (L : Preorder zero zero zero) : Set₁ where

    infix 4 _⊑_
    infix 5 _⊔_

    private
      -- set of labels
      Label : Set
      Label = Carrier L 

    -- flows to relation
    _⊑_     = _∼_ L

    ⊑-refl  = Preorder.refl L
    ⊑-trans = Preorder.trans L

    field

      -- monoidal composition
      _⊔_ : Label → Label → Label
      
      -- unit
      ⊥   : Label
      
      -- monoidal laws
      ⊔-assoc : ∀ {ℓ₁ ℓ₂ ℓ₃} → ℓ₁ ⊔ (ℓ₂ ⊔ ℓ₃) ≡ (ℓ₁ ⊔ ℓ₂) ⊔ ℓ₃
      ⊥-l     : ∀ {ℓ} → ⊥ ⊔ ℓ ≡ ℓ 
      ⊥-r     : ∀ {ℓ} → ℓ ⊔ ⊥ ≡ ℓ

      -- congruence law (seems like a reasonable assumption on preordered monoids)
      ⊔-cong  : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} → ℓ₁ ⊑ ℓ₃ → ℓ₂ ⊑ ℓ₄ → ℓ₁ ⊔ ℓ₂ ⊑ ℓ₃ ⊔ ℓ₄
      
      -- ⊔-comm   : ∀{ℓ ℓ'} → (ℓ ⊔ ℓ') ≡ (ℓ' ⊔ ℓ)

      -- Q: why do we need this?
      -- Decidability criteria
      --_≟_  : (ℓ ℓ' : Label) → Dec (ℓ ≡ ℓ')
      --_?⊑_ : (ℓ ℓ' : Label) → Dec (ℓ ⊑ ℓ')
