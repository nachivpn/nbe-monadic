{-# OPTIONS --postfix-projections #-}

open import Level --using (zero; suc; _⊔_)
open import Algebra.Ordered using (Promonoid)
open import Data.Unit using (⊤; tt)
open import Data.Product using (∃; _×_ ; proj₁ ; proj₂ ; _,_)
open import Relation.Binary using (Preorder)
open import Relation.Binary.PropositionalEquality using (refl)

-- Presheaves on contexts are parametrized by
--
--  * a preordered set of base types,
--  * a promonoid of effects.

module Presheaves {c ℓ₁ ℓ₂}
                  (Base    : Preorder c ℓ₁ ℓ₂)
                  (Effects : Promonoid c ℓ₁ ℓ₂)
                  where

open import Types     Base Effects
open import Coercions Base Effects

-- Presheaves on Contexts and context morphisms

record PSh p : Set (suc (p ⊔ c ⊔ ℓ₂)) where
  field
    on     : Ctx → Set p
    weaken : ∀ {Δ Γ} (Φ : Γ ⊆ Δ) → (on Δ → on Γ)

  -- FIXME: parametrize over a suitable equalitiy and add the functor
  -- laws.

open PSh

-- Natural transformations
--
-- FIXME: add naturality law.

infixr 2 _→'_

_→'_ : ∀ {p q} → PSh p → PSh q → Set _
_→'_ P Q = ∀ {Γ} → (P .on Γ → Q .on Γ)


-- Exponentials, products and the terminal object in the category of
-- presheaves over contexts.  This proves that the latter is a CCC.

infixr 3 _⇒'_
infixl 4 _×'_

_⇒'_ : ∀ {p q} → PSh p → PSh q → PSh _
(P ⇒' Q) .on     Γ        = ∀ {Δ} → Δ ⊆ Γ → P .on Δ → Q .on Δ
(P ⇒' Q) .weaken Φ f Φ' = f (⊆-trans Φ' Φ)

_×'_ : ∀ {p q} → PSh p → PSh q → PSh _
(P ×' Q) .on     Γ         = (P .on Γ) × (Q .on Γ)
(P ×' Q) .weaken Φ (x , y) = (P .weaken Φ x) , (Q .weaken Φ y)

𝟙' : ∀ {p} → PSh p
𝟙' .on     _   = Lift _ ⊤
𝟙' .weaken _ _ = lift tt

∃' : ∀ {a p} → (A : Set a) → (A → PSh p) → PSh _
(∃' A P) .on     Γ         = ∃ λ a → P a .on Γ
(∃' A P) .weaken Φ (a , x) = a , (P a .weaken Φ x)

-- A "sequencing" monad for bindings (essentially the free monad
-- specialized to a sequence of bindings).

data Let {p q} (H : Eff → Tp → PSh p) (Q : PSh q) (Γ : Ctx)
     : Eff → Set (c ⊔ p ⊔ q ⊔ ℓ₂) where
  ret  : Q .on Γ → Let H Q Γ ε
  bind : ∀ {e f a} → H e a .on Γ → Let H Q (a ∷ Γ) f → Let H Q Γ (e ∙ f)
  up   : ∀ {e f} → e ⊑ f → Let H Q Γ e → Let H Q Γ f

weakenLet : ∀ {p q Δ Γ e} (H : Eff → Tp → PSh p) (Q : PSh q)
          → Γ ⊆ Δ → Let H Q Δ e → Let H Q Γ e
weakenLet H Q Φ (ret x)                = ret (Q .weaken Φ x)
weakenLet H Q Φ (bind {e} {f} {a} x y) =
  bind (H e a .weaken Φ x) (weakenLet H Q (refl ∷ Φ) y)
weakenLet H Q Φ (up φ x) = up φ (weakenLet H Q Φ x)

Let' : ∀ {p q} → (Eff → Tp → PSh p) → Eff → PSh q → PSh _
Let' H e Q .on     Γ = Let H Q Γ e
Let' H e Q .weaken   = weakenLet H Q

-- `Let' H` is a graded monad

mapLet : ∀ {h p q e} {H : Eff → Tp → PSh h} {P : PSh p} {Q : PSh q}
       → P →' Q → Let' H e P →' Let' H e Q
mapLet f (ret x)    = ret (f x)
mapLet f (bind x y) = bind x (mapLet f y)
mapLet f (up φ x)   = up φ (mapLet f x)

upLet : ∀ {p q e f} {H : Eff → Tp → PSh p} {Q : PSh q}
      → e ⊑ f → Let' H e Q →' Let' H f Q
upLet φ x = up φ x

returnLet : ∀ {p q} {H : Eff → Tp → PSh p} {Q : PSh q} → Q →' Let' H ε Q
returnLet x = ret x

joinLet : ∀ {p q e f} {H : Eff → Tp → PSh p} {Q : PSh q}
        → Let' H e (Let' H f Q) →' Let' H (e ∙ f) Q
joinLet (ret x)    = up (Eff.reflexive (Eff.Eq.sym (Eff.identityˡ _))) x
joinLet (bind x y) =
  up (Eff.reflexive (Eff.Eq.sym (Eff.assoc _ _ _))) (bind x (joinLet y))
joinLet (up φ x)   = up (Eff.monotonic φ Eff.refl) (joinLet x)

bindLet : ∀ {h p q e f} {H : Eff → Tp → PSh h} {P : PSh p} {Q : PSh q}
        → P →' Let' H e Q → Let' H f P →' Let' H (f ∙ e) Q
bindLet f x = joinLet (mapLet f x)

-- `Let' H` has a monadic strength

strLetCurried : ∀ {h p q e} {H : Eff → Tp → PSh h} {P : PSh p} {Q : PSh q}
              → Let' H e P →' Q ⇒' Let' H e (P ×' Q)
strLetCurried {H = H} {P}     (ret x)    Φ y = ret (P .weaken Φ x , y)
strLetCurried {H = H} {P} {Q} (bind x y) Φ z =
  bind (H _ _ .weaken Φ x )
       (strLetCurried y (refl ∷ Φ) (Q .weaken (_ ∷ˡ ⊆-refl) z))
strLetCurried (up φ x) Φ y = up φ (strLetCurried x Φ y)

strLet : ∀ {h p q e} {H : Eff → Tp → PSh h} {P : PSh p} {Q : PSh q}
       → Let' H e P ×' Q →' Let' H e (P ×' Q)
strLet (x , y) = strLetCurried x ⊆-refl y
