import Relation.Binary as RB
open import Level

module Example where

  module TwoPoint where

    import Relation.Binary.PropositionalEquality as P

    data LH : Set where
      L H : LH

    data _⊑ᴸᴴ_ : LH → LH → Set where
      ⊑ᴸᴴ-H : ∀ {ℓ} → ℓ ⊑ᴸᴴ H
      ⊑ᴸᴴ-L : L ⊑ᴸᴴ L

    ⊑ᴸᴴ-refl : RB.Reflexive _⊑ᴸᴴ_
    ⊑ᴸᴴ-refl {L} = ⊑ᴸᴴ-L
    ⊑ᴸᴴ-refl {H} = ⊑ᴸᴴ-H

    ⊑ᴸᴴ-trans : RB.Transitive _⊑ᴸᴴ_
    ⊑ᴸᴴ-trans a ⊑ᴸᴴ-H = ⊑ᴸᴴ-H
    ⊑ᴸᴴ-trans a ⊑ᴸᴴ-L = a

    _≡ᴸᴴ_ : LH → LH → Set
    _≡ᴸᴴ_ = P._≡_

    ⊑ᴸᴴ-Preorder : RB.Preorder 0ℓ 0ℓ 0ℓ
    ⊑ᴸᴴ-Preorder = record { Carrier = LH
                          ; _≈_ = _≡ᴸᴴ_
                          ; _∼_ = _⊑ᴸᴴ_
                          ; isPreorder = record { isEquivalence = P.isEquivalence
                                                ; reflexive     = λ {P.refl → ⊑ᴸᴴ-refl}
                                                ; trans         = ⊑ᴸᴴ-trans } }

  open TwoPoint

  open import NBELMon (⊑ᴸᴴ-Preorder)
  open import Data.Empty
  open import Relation.Nullary

  main : ¬ (Nf (〈 𝕓 〉 L) ( Ø `, (〈 𝕓 〉 H)))
  main nf with Nf-Prot (Ø `, flows ⊑ᴸᴴ-refl) (〈 𝕓 〉 L) nf
  main nf | flows ()

  main₂ : ¬ (Nf (〈 𝕓 〉 H ⇒ 〈 𝕓 〉 L) Ø)
  main₂ (`λ nf) = main nf
