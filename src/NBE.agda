open import Function
open import Data.Unit
open import Premonoid
open import Data.Product
open import Level using (zero)
open import Relation.Binary hiding (_⇒_)


module NBE
  -- preorder on labels
  (L : Preorder zero zero zero)
  -- preorder on base types
  (B : Preorder zero zero zero)
  -- monoid on labels
  (M : Monoid L)
  where

open Monoid M
open import Type B L
open import Presheaf B L ; open 𝒫

module SubTypeRelation where

  infixr 9 _⋖_

  -- a subtype relation on types
  data _⋖_ : Type → Type → Set where
    subb : ∀ {i j}
           → i ≼ j
           -----------
           → 𝕓 i ⋖ 𝕓 j

    subf : ∀ {a₁ a₂ b₁ b₂}
           → b₁ ⋖ a₁ → a₂ ⋖ b₂
           --------------------
           → a₁ ⇒ a₂ ⋖ b₁ ⇒ b₂

    subm : ∀ {a₁ a₂ ℓ₁ ℓ₂ }
           → ℓ₁ ⊑ ℓ₂ → a₁ ⋖ a₂
           -------------
           → ⟨ a₁ ⟩ ℓ₁ ⋖ ⟨ a₂ ⟩ ℓ₂

  ⋖-refl : ∀ {a} → a ⋖ a
  ⋖-refl {𝕓 i}       = subb ≼-refl
  ⋖-refl {a ⇒ b}     = subf ⋖-refl ⋖-refl
  ⋖-refl {⟨ a₁ ⟩ ℓ₁} = subm ⊑-refl ⋖-refl
  
  ⋖-trans : ∀ {a b c} → a ⋖ b → b ⋖ c → a ⋖ c
  ⋖-trans (subb p)   (subb q)   = subb (≼-trans p q)
  ⋖-trans (subf p q) (subf r s) = subf (⋖-trans r p) (⋖-trans q s)
  ⋖-trans (subm p q) (subm r s) = subm (⊑-trans p r) (⋖-trans q s)

open SubTypeRelation

module Variable where

  data _∈_ : Type → Ctx → Set where
    ze : ∀ {Γ a}   → a ∈ (Γ `, a)
    su : ∀ {Γ a S} → a ∈ Γ → a ∈ (Γ `, S)

  wkenV : ∀ {a} {Γ Δ} → Γ ⊆ Δ → a ∈ Δ → a ∈ Γ
  wkenV (keep e) ze     = ze
  wkenV (keep e) (su v) = su (wkenV e v)
  wkenV (drop e) v      = su (wkenV e v)

open Variable

module Term where

  data Term (Γ : Ctx) : Type → Set where
    `λ    : ∀ {a b} → Term (Γ `, a) b   → Term Γ (a ⇒ b)
    _↑_   : ∀ {a b} → (α : a ⋖ b) → Term Γ a → Term Γ b
    var   : ∀ {a}   → a ∈ Γ → Term Γ a
    _∙_   : ∀ {a b} → Term Γ (a ⇒ b) → Term Γ a → Term Γ b
    η     : ∀ {a}   → Term Γ a → Term Γ (⟨ a ⟩ ⊥)
    _>>=_ : ∀ {a b ℓ ℓ'} → Term Γ (⟨ a ⟩ ℓ) → Term (Γ `, a) (⟨ b ⟩ ℓ') → Term Γ (⟨ b ⟩ (ℓ ⊔ ℓ'))

  wkenT : ∀ {a} {Γ Δ} → Γ ⊆ Δ → Term Δ a → Term Γ a
  wkenT e (`λ t)     = `λ (wkenT (keep e) t)
  wkenT e (α ↑ t)    = α ↑ (wkenT e t)
  wkenT e (var x)    = var (wkenV e x)
  wkenT e (t ∙ t₁)   = wkenT e t ∙ wkenT e t₁
  wkenT e (η t)      = η (wkenT e t)
  wkenT e (t >>= t₁) = wkenT e t >>= wkenT (keep e) t₁

open Term

module NormalForm where

  mutual

     data Ne (Γ : Ctx) : Type → Set where
       var   : ∀ {a}   → a ∈ Γ → Ne Γ a
       _∙_   : ∀ {a b} → Ne Γ (a ⇒ b) → Nf Γ a → Ne Γ b

     data Nf (Γ : Ctx) : Type → Set where
       `λ    : ∀ {a b}      → Nf (Γ `, a) b → Nf Γ (a ⇒ b)
       _↑_   : ∀ {i j}      → 𝕓 i ⋖ 𝕓 j →  Ne Γ (𝕓 i) → Nf Γ (𝕓 j)
       η     : ∀ {a}        → Nf Γ a → Nf Γ (⟨ a ⟩ ⊥)
       _>>=_ : ∀ {a b ℓ ℓ'} → Ne Γ (⟨ a ⟩ ℓ) → Nf (Γ `, a) (⟨ b ⟩ ℓ') → Nf Γ (⟨ b ⟩ (ℓ ⊔ ℓ'))

     wkenNe : ∀ {T} {Γ Δ} → Γ ⊆ Δ → Ne Δ T → Ne Γ T
     wkenNe e (var x) = var (wkenV e x)
     wkenNe e (n ∙ x) = (wkenNe e n) ∙ (wkenNf e x)

     wkenNf : ∀ {T} {Γ Δ} → Γ ⊆ Δ → Nf Δ T → Nf Γ T
     wkenNf e (`λ n)    = `λ (wkenNf (keep e) n)
     wkenNf e (p ↑ x)   = p ↑ (wkenNe e x)
     wkenNf e (η n)     = η (wkenNf e n)
     wkenNf e (x >>= n) = wkenNe e x >>= wkenNf (keep e) n

open NormalForm

module CoverMonad where

  data 𝒞 (Γ : Ctx) (A : 𝒫) : Label → Set where
    ret : A .In Γ → 𝒞 Γ A ⊥ 
    bin : ∀ {a ℓ ℓ'} → Ne Γ (⟨ a ⟩ ℓ) → 𝒞 (Γ `, a) A ℓ' → 𝒞 Γ A (ℓ ⊔ ℓ')

  wken𝒞 : ∀ {A} {Γ Δ} {ℓ} → Γ ⊆ Δ → 𝒞 Δ A ℓ → 𝒞 Γ A ℓ
  wken𝒞 {A} e (ret x) = ret (Wken A e x)
  wken𝒞 e (bin x m) = bin (wkenNe e x) (wken𝒞 (keep e) m)

  𝒞' : Label → 𝒫 → 𝒫
  In   (𝒞' ℓ A) Γ = 𝒞 Γ A ℓ
  Wken (𝒞' ℓ A)   = wken𝒞

  open import Relation.Binary.PropositionalEquality

  cast : ∀ {A} {ℓ ℓ' : Label} → ℓ ≡ ℓ' → 𝒞' ℓ A →' 𝒞' ℓ' A
  cast {A} ℓ≡ℓ′ m  = subst (𝒞 _ A) ℓ≡ℓ′ m

  return𝒞 : ∀ {A} → A →' 𝒞' ⊥ A
  return𝒞 {A} = ret

  map𝒞  : ∀ {A B} {ℓ} → (A →' B) → 𝒞' ℓ A →' 𝒞' ℓ B
  map𝒞 f (ret x)   = ret (f x)
  map𝒞 f (bin x m) = bin x (map𝒞 f m)

  join𝒞 : ∀ {A} {ℓ₁ ℓ₂} → 𝒞' ℓ₁ (𝒞' ℓ₂ A) →' 𝒞' (ℓ₁ ⊔ ℓ₂) A
  join𝒞 (ret x)   = cast (sym ⊥-l) x
  join𝒞 (bin x m) = cast ⊔-assoc (bin x (join𝒞 m))

  bind𝒞 : ∀ {A B} {ℓ₁ ℓ₂} → (A →' 𝒞' ℓ₁ B) → (𝒞' ℓ₂ A →' 𝒞' (ℓ₂ ⊔ ℓ₁) B)
  bind𝒞 f m = join𝒞 (map𝒞 f m)

  -- special operation
  bindExp𝒞 : ∀ {A B Γ} {ℓ₁ ℓ₂} → (A ⇒' 𝒞' ℓ₁ B) .In Γ → (𝒞 Γ A ℓ₂ → 𝒞 Γ B (ℓ₂ ⊔ ℓ₁)) 
  bindExp𝒞 f (ret x) = cast (sym ⊥-l) (f ⊆-refl x)
  bindExp𝒞 f (bin x m) =
    cast ⊔-assoc (bin x (bindExp𝒞 (λ e y → f (⊆-trans e (drop ⊆-refl)) y) m))


open CoverMonad

module Interpretation where

  Tm' : Type → 𝒫
  In   (Tm' a) Γ = Term Γ a
  Wken (Tm' a)   = wkenT
  
  Nf' : Type → 𝒫
  In   (Nf' a) Γ = Nf Γ a
  Wken (Nf' a)   = wkenNf

  Ne' : Type → 𝒫
  In   (Ne' a) Γ = Ne Γ a
  Wken (Ne' a)   = wkenNe

  𝕓' : I → 𝒫
  In   (𝕓' i) Γ              = Σ _ λ j → j ≼ i × Nf Γ (𝕓 j)
  Wken (𝕓' i) e (j , p , nf) = j , p , (wkenNf e nf)

  ⟦_⟧ : Type → 𝒫
  ⟦ 𝕓 i ⟧     = 𝕓' i
  ⟦ a ⇒ b ⟧   = ⟦ a ⟧ ⇒' ⟦ b ⟧
  ⟦ ⟨ a ⟩ ℓ ⟧ = 𝒞' ℓ ⟦ a ⟧

  ⟦_⟧ₑ : Ctx → 𝒫
  ⟦ Ø ⟧ₑ      = 𝟙'
  ⟦ Γ `, a ⟧ₑ = ⟦ Γ ⟧ₑ ×' ⟦ a ⟧

open Interpretation

-- the real deal

lookup : ∀ {a Γ} → a ∈ Γ → ⟦ Γ ⟧ₑ →' ⟦ a ⟧
lookup ze     (_ , v) = v
lookup (su v) (γ , _) = lookup v γ

coerce : ∀ {a b} → a ⋖ b → (⟦ a ⟧ →' ⟦ b ⟧)
coerce {𝕓 i} {𝕓 j} (subb x) (I , p , n) =
  I , ≼-trans p x , n
coerce {.(_ ⇒ _)} {.(_ ⇒ _)} (subf β α) f =
  λ e s → coerce α (f e (coerce β s))
coerce {.(⟨ _ ⟩ _)} (subm x p) m = {!map𝒞 (coerce p)!} -- needs "up"

eval : ∀ {a Γ} → Term Γ a → (⟦ Γ ⟧ₑ →' ⟦ a ⟧)
eval {Γ = Γ} (`λ t) γ     = λ e u → eval t (Wken ⟦ Γ ⟧ₑ e γ , u)
eval {Γ = Γ} (α ↑ t) γ    = coerce α (eval t γ)
eval {Γ = Γ} (var x) γ    = lookup x γ
eval {Γ = Γ} (t ∙ u) γ    = (eval t γ) ⊆-refl (eval u γ)
eval {Γ = Γ} (η t) γ      = ret (eval t γ)
eval {Γ = Γ} (t >>= t₁) γ =
  bindExp𝒞 (λ e x → eval t₁ (Wken ⟦ Γ ⟧ₑ e γ , x)) (eval t γ)

liftNf : ∀ {i j} → i ≼ j → Nf' (𝕓 i) →' Nf' (𝕓 j)
liftNf p ((subb q) ↑ n) = (subb (≼-trans q p)) ↑ n

mutual

  reifyVal : ∀ {a} → ⟦ a ⟧ →' Nf' a
  reifyVal {𝕓 i}    (_ , p , n)  = liftNf p n
  reifyVal {a ⇒ b} f             = `λ (reifyVal (f (drop ⊆-refl) (reflect {a} (var ze))))
  reifyVal {⟨ a ⟩ ℓ} m           = reifyVal𝒞 m

  reifyVal𝒞 : ∀ {a} {ℓ} → 𝒞' ℓ ⟦ a ⟧ →' Nf' (⟨ a ⟩ ℓ)
  reifyVal𝒞 (ret x)   = η (reifyVal x)
  reifyVal𝒞 (bin x m) = x >>= reifyVal𝒞 m

  reflect : ∀ {a} → Ne' a →' ⟦ a ⟧
  reflect {𝕓 i}   n = i , ≼-refl , (⋖-refl ↑ n)
  reflect {_ ⇒ _} n = λ e v → reflect ((wkenNe e n) ∙ (reifyVal v))
  reflect {⟨ a ⟩ ℓ}   n = cast ⊥-r (bin n (ret (reflect {a} (var ze))))

idSubst :  ∀ Γ → ⟦ Γ ⟧ₑ .In Γ
idSubst Ø        = tt
idSubst (Γ `, T) = Wken ⟦ Γ ⟧ₑ (drop ⊆-refl) (idSubst Γ) , reflect {T} (var ze)

reify : ∀{a Γ} → (⟦ Γ ⟧ₑ →' ⟦ a ⟧) → Nf Γ a
reify {a} {Γ} f = reifyVal (f (idSubst Γ))


norm : ∀ {a} → Tm' a →' Nf' a
norm = reify ∘ eval

mutual

  q : ∀ {a} → Nf' a →' Tm' a
  q (`λ n)    = `λ (q n)
  q (p ↑ n)   = p ↑ qNe n
  q (η n)     = η (q n)
  q (x >>= n) = qNe x >>= q n

  qNe : ∀ {a} → Ne' a →' Tm' a
  qNe (var x) = var x
  qNe (x ∙ n) = qNe x ∙ q n

