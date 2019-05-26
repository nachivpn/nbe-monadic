open import Level
import Relation.Binary as RB
module Example (B : RB.Preorder 0ℓ 0ℓ 0ℓ) where

  import Data.Unit as U
  import Data.Unit.Properties as UP
  import Relation.Binary.PropositionalEquality as P

  open import TwoPoint as TP
  open import NBE (TP.⊑LH-Preorder) (record { Carrier = U.⊤ ; _≈_ = P._≡_ ; _∼_ = U._≤_ ; isPreorder = UP.≤-isPreorder }) (TP.⊑LH-Monoid)
  

 
  ex1lemma : Nf ((Ø `, 𝕓 U.tt) `, (⟨ 𝕓 U.tt ⟩ H)) (⟨ 𝕓 U.tt ⟩ L) → Set
  ex1lemma x = {!!}
  -- ex1lemma (c ↑ var (su ze)) = {!!}
  -- ex1lemma (c ↑ (n ∙ x)) = {!!}
