{-# OPTIONS --allow-unsolved-metas #-}
module TwoPoint where

  open import Level
  open import Relation.Binary
  -- open import Algebra
  import Relation.Binary.PropositionalEquality as P

  open import Premonoid
  open Preorder

  data LH : Set where
    L H   : LH

  data _⊑LH_ : LH → LH → Set where
    ⊑-H : ∀ {ℓ} → ℓ ⊑LH H
    ⊑-L : L ⊑LH L

  ⊑LH-refl : Reflexive _⊑LH_
  ⊑LH-refl {L} = ⊑-L
  ⊑LH-refl {H} = ⊑-H

  ⊑LH-trans : Transitive _⊑LH_
  ⊑LH-trans p ⊑-H = ⊑-H
  ⊑LH-trans p ⊑-L = p

  ⊑LH-Preorder : Preorder 0ℓ 0ℓ 0ℓ
  ⊑LH-Preorder = record { Carrier = LH ; _≈_ = P._≡_ ; _∼_ = _⊑LH_
                        ; isPreorder = record { isEquivalence = P.isEquivalence ; reflexive = λ {P.refl → ⊑LH-refl} ; trans = ⊑LH-trans } }


  _⊔-LH_ : LH → LH → LH 
  L ⊔-LH L = L
  L ⊔-LH H = H
  H ⊔-LH b = H

  ⊑LH-Monoid : Monoid ⊑LH-Preorder
  ⊑LH-Monoid = record
                 { _⊔_ = _⊔-LH_ ; ⊥ = L ; ⊔-assoc = {!!} ; ⊥-l = {!!} ; ⊥-r = {!!} ; ⊔-cong = {!!} }

