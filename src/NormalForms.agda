open import Level using (_⊔_; lift)
open import Algebra.Ordered using (Promonoid)
import Data.List.Relation.Binary.Sublist.Setoid as Sublist
open import Data.List.Relation.Unary.Any using (Any)
open import Data.Product using (_,_; proj₁; proj₂; ∃; _×_)
open import Data.Unit using (tt)
open import Relation.Binary using (Preorder)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

-- Normal forms are parametrized by
--
--  * a preordered set of base types,
--  * a preordered monoid of effects.
--
-- These two preorders generate the subtyping relation.

module NormalForms {c ℓ₁ ℓ₂}
                   (Base    : Preorder c ℓ₁ ℓ₂)
                   (Effects : Promonoid c ℓ₁ ℓ₂)
                   where

open import Types      Base Effects
open import Coercions  Base Effects
open import Terms      Base Effects
open import Presheaves Base Effects

open PSh

infixr 8 _·_ _*_
infix  4 _⇇_ _⇉_ _⇇_⇉_
infixr 4 _,_
infixr 2 _∋_

-- The syntax of intrinsically *bidirectionally* typed normal forms

mutual

  -- Values: types are checked

  data _⇇_ (Γ : Ctx) : Tp → Set (c ⊔ ℓ₂) where

    ƛ : ∀ {a b}
      → a ∷ Γ ⇇ b
        --------- (abstraction)
      → Γ ⇇ a ⇒ b

    ⟨⟩ : --------- (unit element)
         Γ ⇇ unit

    _,_ : ∀ {a b}
        → Γ ⇇ a
        → Γ ⇇ b
          --------- (pairing)
        → Γ ⇇ a 𝕩 b
 
    _*_ : ∀ {i j}
        → i ≤ j
        → Γ ⇉ bs i
        ---------- (subsumption)
        → Γ ⇇ bs j

    up : ∀ {e f a}
       → e ⊑ f
       → Γ ⇇ a ⇉ e
         ----------- (computation)
       → Γ ⇇ ⟨ f ⟩ a


  -- Computations: types are checked, effects are synthesized 

  data _⇇_⇉_ (Γ : Ctx) : Tp → Eff → Set (c ⊔ ℓ₂) where

    ◇ : ∀ {a}
      → Γ ⇇ a
        --------- (monadic unit/return/diamond)
      → Γ ⇇ a ⇉ ε

    _>>=_ : ∀ {e f a b}
          → Γ ⇉ ⟨ e ⟩ a
          → a ∷ Γ ⇇ b ⇉ f
            ------------- (monadic bind/Kleisli extension)
          → Γ ⇇ b ⇉ e ∙ f


  -- Neutrals: types are syntesized

  data _⇉_ (Γ : Ctx) : Tp → Set (c ⊔ ℓ₂) where

    var : ∀ {a}
        → a ∈ Γ
        ------- (variable lookup)
        → Γ ⇉ a

    fst : ∀ {a b}
        → Γ ⇉ a 𝕩 b
        ----------- (first projection)
        → Γ ⇉ a

    snd : ∀ {a b}
        → Γ ⇉ a 𝕩 b
        ----------- (second projection)
        → Γ ⇉ b

    _·_ : ∀ {a b}
        → Γ ⇉ a ⇒ b
        → Γ ⇇ a
        ----------- (application)
        → Γ ⇉ b

    _∋_ : ∀ a
        → Γ ⇇ a
        ------- (ascription)
        → Γ ⇉ a

-- Weakening of normal forms

mutual

  weakenVal : ∀ {a} {Γ Δ} → Γ ⊆ Δ → Δ ⇇ a → Γ ⇇ a
  weakenVal Φ (ƛ u)    = ƛ (weakenVal (refl ∷ Φ) u)
  weakenVal Φ ⟨⟩       = ⟨⟩
  weakenVal Φ (u , v)  = weakenVal Φ u , weakenVal Φ v
  weakenVal Φ (α * n)  = α * weakenNe Φ n
  weakenVal Φ (up φ c) = up φ (weakenCmp Φ c)

  weakenCmp : ∀ {a e} {Γ Δ} → Γ ⊆ Δ → Δ ⇇ a ⇉ e → Γ ⇇ a ⇉ e
  weakenCmp Φ (◇ u)     = ◇ (weakenVal Φ u)
  weakenCmp Φ (n >>= c) = weakenNe Φ n >>= weakenCmp (refl ∷ Φ) c

  weakenNe : ∀ {a} {Γ Δ} → Γ ⊆ Δ → Δ ⇉ a → Γ ⇉ a
  weakenNe Φ (var x) = var (weakenVar Φ x)
  weakenNe Φ (fst n) = fst (weakenNe Φ n)
  weakenNe Φ (snd n) = snd (weakenNe Φ n)
  weakenNe Φ (n · u) = weakenNe Φ n · weakenVal Φ u
  weakenNe Φ (a ∋ u) = a ∋ weakenVal Φ u

-- Normal forms are presheaves

Val : Tp → PSh (c ⊔ ℓ₂)
(Val a) .on     Γ = Γ ⇇ a
(Val a) .weaken Φ = weakenVal Φ

Cmp : Eff → Tp → PSh (c ⊔ ℓ₂)
(Cmp e a) .on     Γ             = ∃ λ f → f ⊑ e × Γ ⇇ a ⇉ f 
(Cmp e a) .weaken Φ (f , φ , c) = f , φ , weakenCmp Φ c

Ne : Tp → PSh (c ⊔ ℓ₂)
(Ne a) .on     Γ = Γ ⇉ a
(Ne a) .weaken Φ = weakenNe Φ

infixr 9 ⟨_⟩'_

⟨_⟩'_ : ∀ {p} → Eff → PSh p → PSh _
⟨_⟩'_ = Let' (λ e a → Ne (⟨ e ⟩ a))

-- Interpretation of types

⟦_⟧ : Tp → PSh (c ⊔ ℓ₂)
⟦ bs i    ⟧ = ∃' (∃ λ j → j ≤ i) λ{ (j , ι) → Ne (bs j) }
⟦ unit    ⟧ = 𝟙'
⟦ a 𝕩 b   ⟧ = ⟦ a ⟧ ×' ⟦ b ⟧
⟦ a ⇒ b   ⟧ = ⟦ a ⟧ ⇒' ⟦ b ⟧
⟦ ⟨ e ⟩ a ⟧ = ⟨ e ⟩' ⟦ a ⟧

⟦_⟧Ctx : Ctx → PSh (c ⊔ ℓ₂)
⟦ []    ⟧Ctx = 𝟙'
⟦ a ∷ Γ ⟧Ctx = ⟦ a ⟧ ×' ⟦ Γ ⟧Ctx

-- Interpretation of coercions and terms (evaluation)

lookupVal : ∀ {a Γ} → a ∈ Γ → ⟦ Γ ⟧Ctx →' ⟦ a ⟧
lookupVal (here refl) (v , _) = v
lookupVal (there x)   (_ , γ) = lookupVal x γ

coerce : ∀ {a b} → a <: b → (⟦ a ⟧ →' ⟦ b ⟧)
coerce (coe ι)     ((j , κ) , n) = (j , Bs.trans κ ι) , n
coerce unit        x             = x
coerce (α ⇒ β)     f Φ x         = coerce β (f Φ (coerce α x))
coerce (α 𝕩 β)     (x , y)       = (coerce α x) , (coerce β y)
coerce (⟨ φ ⟩ α)   x             = upLet φ (mapLet (coerce α) x)
coerce refl        x             = x
coerce (trans α β) x             = coerce β (coerce α x)

eval : ∀ {a Γ} → Γ ⊢ a → (⟦ Γ ⟧Ctx →' ⟦ a ⟧)
eval         (var x)   γ = lookupVal x γ
eval         ⟨⟩        γ = lift tt
eval         (t , u)   γ = eval t γ , eval u γ
eval         (fst t)   γ = proj₁ (eval t γ) 
eval         (snd t)   γ = proj₂ (eval t γ)
eval {a} {Γ} (ƛ t)     γ = λ Φ x → eval t (x , ⟦ Γ ⟧Ctx .weaken Φ γ)
eval         (t · u)   γ = (eval t γ) ⊆-refl (eval u γ)
eval         (◇ t)     γ = returnLet (eval t γ)
eval {a} {Γ} (t >>= u) γ =
  bindLet (eval u) (strLet {Q = ⟦ Γ ⟧Ctx} (eval t γ , γ))
eval (α * t) γ = coerce α (eval t γ)
eval (a ∋ t) γ = eval t γ

-- Reflection/reification of terms

mutual

  reifyVal : ∀ {a} → ⟦ a ⟧ →' Val a
  reifyVal {bs i}    ((j , ι) , n) = ι * n
  reifyVal {unit}    _             = ⟨⟩
  reifyVal {a 𝕩 b}   (x , y)       = reifyVal x , reifyVal y
  reifyVal {a ⇒ b}   f             =
    ƛ (reifyVal (f (_ ∷ˡ ⊆-refl) (reflect {a} (var (here refl)))))
  reifyVal {⟨ e ⟩ a} x             = let _ , φ , c = reifyCmp x in up φ c

  reifyCmp : ∀ {e a} → ⟨ e ⟩' ⟦ a ⟧ →' Cmp e a
  reifyCmp (ret x)    = _ , Eff.refl , ◇ (reifyVal x)
  reifyCmp (bind x y) =
    let e , φ , y' = reifyCmp y
    in  _ ∙ e , Eff.monotonic Eff.refl φ , x >>= y'
  reifyCmp (up φ x)   =
    let e , ψ , y = reifyCmp x
    in  e , Eff.trans ψ φ , y

  reflect : ∀ {a} → Ne a →' ⟦ a ⟧
  reflect {bs i}    n = (i , Bs.refl) , n
  reflect {unit}    n = lift tt
  reflect {a 𝕩 b}   n = reflect (fst n) , reflect (snd n)
  reflect {a ⇒ b}   n = λ Φ x → reflect (weakenNe Φ n · reifyVal x) 
  reflect {⟨ e ⟩ a} n =
    up (Eff.reflexive (Eff.identityʳ e))
       (bind n (ret (reflect {a} (var (here refl)))))

idSubst :  ∀ Γ → ⟦ Γ ⟧Ctx .on Γ
idSubst []      = lift tt
idSubst (a ∷ Γ) =
  (reflect {a} (var (here refl))) ,
  (⟦ Γ ⟧Ctx .weaken (a ∷ˡ ⊆-refl) (idSubst Γ))

reify : ∀ {Γ a} → (⟦ Γ ⟧Ctx →' ⟦ a ⟧) → Γ ⇇ a
reify {Γ} f = reifyVal (f (idSubst Γ))

norm : ∀ {Γ a} → Γ ⊢ a → Γ ⇇ a
norm t = reify (eval t)
