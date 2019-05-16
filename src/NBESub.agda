module NBESub where

  open import Relation.Binary hiding (_⇒_)
  open import Function using (_∘′_)

  module _ (I : Set) (_≼_ : I → I → Set)
                     (≼-refl  : Reflexive _≼_ )
                     (≼-trans : Transitive _≼_) where

    data Type  : Set where
      𝕓   : (i : I)      → Type
      _⇒_ : (T S : Type) → Type
      𝕋   : Type         → Type
     
    data Ctx : Set where
      Ø    : Ctx
      _`,_ : Ctx → (T : Type) → Ctx

    infixr 25 _⇒_

    module OPE where

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

    open OPE

    module Variable where

      data _∈_ : Type → Ctx → Set where
        ze : ∀ {Γ T}   → T ∈ (Γ `, T)
        su : ∀ {Γ T S} → T ∈ Γ → T ∈ (Γ `, S)

      weakⱽ : ∀ {T} {Γ Δ} → Γ ⊆ Δ → T ∈ Δ → T ∈ Γ
      weakⱽ (keep Γ⊆Δ) ze     = ze
      weakⱽ (keep Γ⊆Δ) (su v) = su (weakⱽ Γ⊆Δ v)
      weakⱽ (drop Γ⊆Δ) v      = su (weakⱽ Γ⊆Δ v)

    open Variable

    module Subtyping where

      data _⋖_ : Type → Type → Set where
        up𝕓    : ∀ {i j}
              → i ≼ j
              -----------
              → 𝕓 i ⋖ 𝕓 j

        ₍_₎⁽_⁾ : ∀ {T₁ T₂ S₁ S₂}
              → S₁ ⋖ T₁ → T₂ ⋖ S₂
              --------------------
              → T₁ ⇒ T₂ ⋖ S₁ ⇒ S₂

        up𝕋    : ∀ {S₁ S₂}
               → S₁ ⋖ S₂
               -------------
               → 𝕋 S₁ ⋖ 𝕋 S₂

      ⋖-refl : ∀ {T} → T ⋖ T
      ⋖-refl {𝕓 i}    = up𝕓 ≼-refl
      ⋖-refl {T ⇒ S}  = ₍ ⋖-refl ₎⁽ ⋖-refl ⁾
      ⋖-refl {𝕋 S}    = up𝕋 ⋖-refl     

      ⋖-trans : ∀ {S T Q} → S ⋖ T → T ⋖ Q → S ⋖ Q
      ⋖-trans (up𝕓 p) (up𝕓 q)       = up𝕓 (≼-trans p q)
      ⋖-trans ₍ a ₎⁽ b ⁾ ₍ p ₎⁽ q ⁾ = ₍ (⋖-trans p a) ₎⁽ (⋖-trans b q) ⁾
      ⋖-trans (up𝕋 x) (up𝕋 y)       = up𝕋 (⋖-trans x y)

    open Subtyping

    data Term (Γ : Ctx) : Type → Set where
      `λ    : ∀ {T S} → Term (Γ `, T) S   → Term Γ (T ⇒ S)
      _↑_   : ∀ {T S} → (α : T ⋖ S) → Term Γ T → Term Γ S
      var   : ∀ {T}   → T ∈ Γ → Term Γ T
      _∘_   : ∀ {T S} → Term Γ (T ⇒ S) → Term Γ T → Term Γ S
      η     : ∀ {T}   → Term Γ T → Term Γ (𝕋 T)
      _>>=_ : ∀ {T S} → Term Γ (𝕋 T) → Term (Γ `, T) (𝕋 S) → Term Γ (𝕋 S)

    weakᵀ : ∀ {T} {Γ Δ} → Γ ⊆ Δ → Term Δ T → Term Γ T
    weakᵀ e (`λ t)     = `λ (weakᵀ (keep e) t)
    weakᵀ e (α ↑ t)    = α ↑ (weakᵀ e t)
    weakᵀ e (var x)    = var (weakⱽ e x)
    weakᵀ e (t ∘ t₁)   = weakᵀ e t ∘ weakᵀ e t₁
    weakᵀ e (η t)      = η (weakᵀ e t)
    weakᵀ e (t >>= t₁) = weakᵀ e t >>= weakᵀ (keep e) t₁
    
    record 𝒫 : Set₁ where
      field
        In   : Ctx → Set
        Wken : ∀ {Δ Γ} (Γ⊆Δ : Γ ⊆ Δ) → (In Δ → In Γ)

    open 𝒫
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

    mutual
    
      data Ne (Γ : Ctx) : Type → Set where
        var   : ∀ {a}   → a ∈ Γ → Ne Γ a
        app   : ∀ {a b} → Ne Γ (a ⇒ b) → Nf Γ a → Ne Γ b
        
      data Nf (Γ : Ctx) : Type → Set where
        abs   : ∀ {a b} → Nf (Γ `, a) b → Nf Γ (a ⇒ b)
        neu   : ∀ {i j} → 𝕓 i ⋖ 𝕓 j →  Ne Γ (𝕓 i) → Nf Γ (𝕓 j)
        η     : ∀ {a}   → Nf Γ a → Nf Γ (𝕋 a)
        _>>=_ : ∀ {a b} → Ne Γ (𝕋 a) → Nf (Γ `, a) (𝕋 b) → Nf Γ (𝕋 b)
        
    _→'_ : (P Q : 𝒫) → Set
    _→'_ P Q = ∀ {Γ} → (P .In Γ → Q .In Γ)

    mutual
    
      wkenⁿᵉ : ∀ {T} {Γ Δ} → Γ ⊆ Δ → Ne Δ T → Ne Γ T
      wkenⁿᵉ e (var x)   = var (weakⱽ e x)
      wkenⁿᵉ e (app n x) = app (wkenⁿᵉ e n) (wkenⁿᶠ e x)

      wkenⁿᶠ : ∀ {T} {Γ Δ} → Γ ⊆ Δ → Nf Δ T → Nf Γ T
      wkenⁿᶠ e (abs n)   = abs (wkenⁿᶠ (keep e) n)
      wkenⁿᶠ e (neu p x) = neu p (wkenⁿᵉ e x)
      wkenⁿᶠ e (η n)     = η (wkenⁿᶠ e n)
      wkenⁿᶠ e (x >>= n) = wkenⁿᵉ e x >>= wkenⁿᶠ (keep e) n

    Nf' : Type → 𝒫
    In   (Nf' T) Γ = Nf Γ T
    Wken (Nf' T)   = wkenⁿᶠ
    
    Ne' : Type → 𝒫
    In   (Ne' T) Γ = Ne Γ T
    Wken (Ne' T)   = wkenⁿᵉ

    upNf : ∀ {i j} → i ≼ j → Nf' (𝕓 i) →' Nf' (𝕓 j)
    upNf p (neu (up𝕓 q) n) = neu (up𝕓 (≼-trans q p)) n

    data 𝒯 (Γ : Ctx) (A : 𝒫) : Set where
      ret : A .In Γ → 𝒯 Γ A 
      bin : ∀ {S} → Ne Γ (𝕋 S) → 𝒯 (Γ `, S) A → 𝒯 Γ A

    wken𝒯 : ∀ {A} {Γ Δ} → Γ ⊆ Δ → 𝒯 Δ A → 𝒯 Γ A
    wken𝒯 {A} e (ret x) = ret (Wken A e x)
    wken𝒯 e (bin x m) = bin (wkenⁿᵉ e x) (wken𝒯 (keep e) m)

    -- 𝒯' is a monad in the category of presheaves
    𝒯' : 𝒫 → 𝒫
    In   (𝒯' A) Γ = 𝒯 Γ A
    Wken (𝒯' A)   = wken𝒯
    
    return𝒯' : ∀ {A} → A →' 𝒯' A
    return𝒯' = ret
    
    map𝒯'  : ∀ {A B} → (A →' B) → 𝒯' A →' 𝒯' B
    map𝒯' f (ret x)   = ret (f x)
    map𝒯' f (bin x m) = bin x (map𝒯' f m)

    join𝒯' : ∀ {A} → 𝒯' (𝒯' A) →' 𝒯' A
    join𝒯' (ret x)   = x
    join𝒯' (bin x m) = bin x (join𝒯' m)

    bind𝒯' : ∀ {A B} → (A →' 𝒯' B) → (𝒯' A →' 𝒯' B) 
    bind𝒯' f m = join𝒯' (map𝒯' f m)

    -- special operation on 𝒯' 
    bindExp𝒯 : ∀ {A B Γ} → (A ⇒' 𝒯' B) .In Γ → (𝒯 Γ A → 𝒯 Γ B) 
    bindExp𝒯 f (ret x) = f ⊆-refl x
    bindExp𝒯 f (bin x m) =
      bin x (bindExp𝒯 (λ e y → f (⊆-trans e (drop ⊆-refl)) y) m)

    -- type interpretations
    
    𝕓' : I → 𝒫
    In   (𝕓' i) Γ              = Σ I λ j → j ≼ i × Nf Γ (𝕓 j)
    Wken (𝕓' i) e (j , p , nf) = j , p , (wkenⁿᶠ e nf)

    ⟦_⟧ : Type → 𝒫
    ⟦ 𝕓 i ⟧   = 𝕓' i
    ⟦ T ⇒ S ⟧ = ⟦ T ⟧ ⇒' ⟦ S ⟧
    ⟦ 𝕋 S ⟧   = 𝒯' ⟦ S ⟧

    ⟦_⟧ₑ : Ctx → 𝒫
    ⟦ Ø ⟧ₑ      = 𝟙'
    ⟦ Γ `, T ⟧ₑ = ⟦ Γ ⟧ₑ ×' ⟦ T ⟧

    -- the real deal

    lookup : ∀ {T Γ} → T ∈ Γ → ⟦ Γ ⟧ₑ →' ⟦ T ⟧
    lookup ze     (_ , v) = v
    lookup (su v) (γ , _) = lookup v γ

    cast : ∀ {T S} → T ⋖ S → (⟦ T ⟧ →' ⟦ S ⟧)
    cast {𝕓 i} {𝕓 j} (up𝕓 x) (I , p , n) =
      I , ≼-trans p x , n
    cast {.(_ ⇒ _)} {.(_ ⇒ _)} ₍ β ₎⁽ α ⁾ f =
      λ Δ⊆Γ s → cast α (f Δ⊆Γ (cast β s))
    cast {.(𝕋 _)} {.(𝕋 _)} (up𝕋 p) m =
      map𝒯' (cast p) m
    
    eval : ∀ {T Γ} → Term Γ T → (⟦ Γ ⟧ₑ →' ⟦ T ⟧)
    eval {Γ = Γ} (`λ t) γ     = λ e u → eval t (Wken ⟦ Γ ⟧ₑ e γ , u)
    eval {Γ = Γ} (α ↑ t) γ    = cast α (eval t γ)
    eval {Γ = Γ} (var x) γ    = lookup x γ
    eval {Γ = Γ} (t ∘ u) γ    = (eval t γ) ⊆-refl (eval u γ)
    eval {Γ = Γ} (η t) γ      = ret (eval t γ)
    eval {Γ = Γ} (t >>= t₁) γ =
      bindExp𝒯 (λ e x → eval t₁ (Wken ⟦ Γ ⟧ₑ e γ , x)) (eval t γ)
      
    mutual
    
      reifyVal : ∀ {T} → ⟦ T ⟧ →' Nf' T
      reifyVal {𝕓 i} (j , p , n) = upNf p n
      reifyVal {T ⇒ T₁} f        = abs (reifyVal (f (drop ⊆-refl) (reflect {T} (var ze))))
      reifyVal {𝕋 a}    y        = reifyVal𝕋 y

      reifyVal𝕋 : ∀{S} → 𝒯' ⟦ S ⟧ →' Nf' (𝕋 S)
      reifyVal𝕋 (ret x)   = η (reifyVal x)
      reifyVal𝕋 (bin x m) = x >>= reifyVal𝕋 m
      
      reflect : ∀ {T} → Ne' T →' ⟦ T ⟧
      reflect {𝕓 i}    n = i , ≼-refl , (neu ⋖-refl n)
      reflect {T ⇒ T₁} n = λ e v → reflect (app (wkenⁿᵉ e n) (reifyVal v))
      reflect {𝕋 a}    n = bin n (ret (reflect {a} (var ze)))

    idSubst :  ∀ Γ → ⟦ Γ ⟧ₑ .In Γ
    idSubst Ø        = tt
    idSubst (Γ `, T) = Wken ⟦ Γ ⟧ₑ (drop ⊆-refl) (idSubst Γ) , reflect {T} (var ze)
    
    reify : ∀{T Γ} → (⟦ Γ ⟧ₑ →' ⟦ T ⟧) → Nf Γ T
    reify {T} {Γ} f = reifyVal (f (idSubst Γ))

    norm : ∀ {T Γ} → Term Γ T → Nf Γ T
    norm = reify ∘′ eval
