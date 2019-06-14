import Relation.Binary as RB
open import Level

module Example (Pre : RB.Preorder 0ℓ 0ℓ 0ℓ) where

  open import NBELMon (Pre)
  open import Data.Empty
  open import Relation.Nullary
  open import Relation.Binary.PropositionalEquality
  open import Data.Sum

  Bool : Type
  Bool = 𝟙 + 𝟙

  True : ∀ {Γ} → Nf Bool Γ
  True = inl unit

  False : ∀ {Γ} → Nf Bool Γ
  False = inr unit

  -- general lemma about normal forms of programs from secret
  -- inputs to public booleans that does not assume anything
  -- but the preorder on the monad labels
  nf-lemma₁ : ∀ {a} {ℓᴸ ℓᴴ}
            → ¬ (ℓᴴ ⊑ ℓᴸ)
            → (n : Nf (〈 ℓᴴ 〉 a ⇒ 〈 ℓᴸ 〉 Bool) Ø)
            → (n ≡ `λ (η True)) ⊎ (n ≡ `λ (η False))
  nf-lemma₁ ℓᴴ⋢ℓᴸ (`λ (η (inl unit))) = inj₁ refl
  nf-lemma₁ ℓᴴ⋢ℓᴸ (`λ (η (inl (case x n n₁))))
    with neutrality x
  ... | here ()
  ... | there ()
  nf-lemma₁ ℓᴴ⋢ℓᴸ (`λ (η (inr unit))) = inj₂ refl
  nf-lemma₁ ℓᴴ⋢ℓᴸ (`λ (η (inr (case x n n₁))))
    with neutrality x
  ... | here ()
  ... | there ()
  nf-lemma₁ ℓᴴ⋢ℓᴸ (`λ (η (case x k₁ k₂)))
    with neutrality x
  ... | here ()
  ... | there ()
  nf-lemma₁ ℓᴴ⋢ℓᴸ (`λ (c ↑ m ≫= k))
    with neutrality m
  ... | here refl = ⊥-elim (ℓᴴ⋢ℓᴸ c)
  nf-lemma₁ ℓᴴ⋢ℓᴸ (`λ (case x k₁ k₂))
    with neutrality x
  ... | here ()
  ... | there ()
  nf-lemma₁ ℓᴴ⋢ℓᴸ (case x _ _)
    with neutrality x
  ... | ()
