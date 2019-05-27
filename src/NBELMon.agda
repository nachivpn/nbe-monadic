{-# OPTIONS --allow-unsolved-metas #-}
import Relation.Binary as RB
open import Level

module NBELMon (Pre : RB.Preorder 0ℓ 0ℓ 0ℓ)where

  Label = RB.Preorder.Carrier Pre
  _⊑_   = RB.Preorder._∼_ Pre

  module TypeModule where

    -- Types are either function space and
    -- a base type for every i ∈ I
    data Type  : Set where
      𝟙     :                 Type
      𝕓     :                 Type
      _⇒_   : (a b : Type)  → Type
      _+_   : (a b : Type)  → Type
      〈_〉_   : (a : Type) (ℓ : Label) → Type
 
    infixr 10 _⇒_

    -- Ctx as a snoc list of types
    data Ctx : Set where
      Ø    : Ctx
      _`,_ : Ctx → Type → Ctx

  open TypeModule public

  module Weakening where

    -- Weakening over contexts Γ ⊆ Δ to be read as:
    -- Γ is weaker (contains possibly more types) than Δ
    -- Δ is thinner (contains possibly less types) than Γ
    data _⊆_ : Ctx → Ctx → Set where
      base : Ø ⊆ Ø
      keep : ∀ {T Γ Δ} → Γ ⊆ Δ → (Γ `, T) ⊆ (Δ `, T)
      drop : ∀ {T Γ Δ} → Γ ⊆ Δ → (Γ `, T) ⊆ Δ

    -- Weakenings are a preorder relation
    ⊆-refl : RB.Reflexive _⊆_
    ⊆-refl {Ø}      = base
    ⊆-refl {Γ `, T} = keep ⊆-refl

    ⊆-trans : RB.Transitive _⊆_
    ⊆-trans base q = q
    ⊆-trans (keep p) (keep q) = keep (⊆-trans p q)
    ⊆-trans (keep p) (drop q) = drop (⊆-trans p q)
    ⊆-trans (drop p) q        = drop (⊆-trans p q)

  open Weakening public

  module Variable where

    -- De Bruijn index into a context
    data _∈_ : Type → Ctx → Set where
      ze : ∀ {Γ a}   → a ∈ (Γ `, a)
      su : ∀ {Γ a S} → a ∈ Γ → a ∈ (Γ `, S)

    wkenⱽ : ∀ {a} {Γ Δ} → Γ ⊆ Δ → a ∈ Δ → a ∈ Γ
    wkenⱽ (keep e) ze     = ze
    wkenⱽ (keep e) (su v) = su (wkenⱽ e v)
    wkenⱽ (drop e) v      = su (wkenⱽ e v)

  open Variable public

  module TermM where

    data Term : Type → Ctx → Set where
      unit  : ∀ {Γ} → Term 𝟙 Γ
      `λ    : ∀ {Γ} {a b} → Term b (Γ `, a) → Term (a ⇒ b) Γ
      var   : ∀ {Γ} {a}   → a ∈ Γ → Term a Γ
      _∙_   : ∀ {Γ} {a b} → Term (a ⇒ b) Γ → Term a Γ → Term b Γ
      _↑_   : ∀ {ℓᴸ ℓᴴ} {Γ} {a} → ℓᴸ ⊑ ℓᴴ → Term (〈 a 〉 ℓᴸ) Γ → Term (〈 a 〉 ℓᴴ) Γ
      η     : ∀ {ℓ} {Γ} {a}    → Term a Γ → Term (〈 a 〉 ℓ) Γ
      _≫=_ : ∀ {ℓ} {Γ} {a b} → Term (〈 a 〉 ℓ) Γ → Term (〈 b 〉 ℓ) (Γ `, a) → Term (〈 b 〉 ℓ) Γ
      inl   : ∀ {Γ} {a b} → Term a Γ → Term (a + b) Γ
      inr   : ∀ {Γ} {a b} → Term b Γ → Term (a + b) Γ
      case  : ∀ {Γ} {a b c} → Term (a + b) Γ → Term c (Γ `, a) → Term c (Γ `, b) → Term c Γ

    wkenTm : ∀ {a} {Γ Δ} → Γ ⊆ Δ → Term a Δ → Term a Γ
    wkenTm e unit = unit
    wkenTm e (`λ t)    = `λ (wkenTm (keep e) t)
    wkenTm e (var x)   = var (wkenⱽ e x)
    wkenTm e (t ∙ t₁)  = wkenTm e t ∙ wkenTm e t₁
    wkenTm e (η t)     = η (wkenTm e t)
    wkenTm e (t ≫= k) = wkenTm e t ≫= wkenTm (keep e) k
    wkenTm e (x ↑ t)   = x ↑ wkenTm e t
    wkenTm e (inl t) = inl (wkenTm e t)
    wkenTm e (inr t) = inr (wkenTm e t)
    wkenTm e (case t t₁ t₂) = case (wkenTm e t) (wkenTm (keep e) t₁) (wkenTm (keep e) t₂)
    
  open TermM public

  module NormalForm where

  mutual

    data Ne : Type → Ctx → Set where
      var   : ∀ {Γ} {a}   → a ∈ Γ → Ne a Γ
      _∙_   : ∀ {Γ} {a b} → Ne (a ⇒ b) Γ → Nf a Γ → Ne b Γ
      _↑_   : ∀ {ℓᴸ ℓᴴ} {Γ} {a} → ℓᴸ ⊑ ℓᴴ → Ne (〈 a 〉 ℓᴸ) Γ → Ne (〈 a 〉 ℓᴴ) Γ

    data Nf : Type → Ctx → Set where
      unit  : ∀ {Γ} → Nf 𝟙 Γ 
      `λ    : ∀ {Γ} {a b}      → Nf b (Γ `, a) → Nf (a ⇒ b) Γ
      𝕓     : ∀ {Γ}            → Ne 𝕓 Γ   → Nf 𝕓 Γ
      η     : ∀ {ℓ} {Γ}  {a}   → Nf a Γ → Nf (〈 a 〉 ℓ) Γ
      _≫=_ : ∀ {ℓ} {Γ} {a b}  → Ne (〈 a 〉 ℓ) Γ → Nf (〈 b 〉 ℓ) (Γ `, a) → Nf (〈 b 〉 ℓ) Γ
      inl   : ∀ {Γ} {a b} → Nf a Γ → Nf (a + b) Γ
      inr   : ∀ {Γ} {a b} → Nf b Γ → Nf (a + b) Γ
      case  : ∀ {Γ} {a b c} → Ne (a + b) Γ → Nf c (Γ `, a) → Nf c (Γ `, b) → Nf c Γ

    wkenNe : ∀ {T} {Γ Δ} → Γ ⊆ Δ → Ne T Δ → Ne T Γ
    wkenNe e (var x) = var (wkenⱽ e x)
    wkenNe e (n ∙ x) = (wkenNe e n) ∙ (wkenNf e x)
    wkenNe e (c ↑ n) = c ↑ wkenNe e n

    wkenNf : ∀ {T} {Γ Δ} → Γ ⊆ Δ → Nf T Δ → Nf T Γ
    wkenNf e unit      = unit
    wkenNf e (`λ n)    = `λ (wkenNf (keep e) n)
    wkenNf e (η m)     = η (wkenNf e m)
    wkenNf e (𝕓 n)     = 𝕓 (wkenNe e n)
    wkenNf e (x ≫= m) = (wkenNe e x) ≫= wkenNf (keep e) m
    wkenNf e (inl n)   = inl (wkenNf e n)
    wkenNf e (inr n)   = inr (wkenNf e n)
    wkenNf e (case x n₁ n₂) = case (wkenNe e x) (wkenNf (keep e) n₁) (wkenNf (keep e) n₂)

  open NormalForm public

  open import Data.Product
  open import Data.Unit hiding (_≤_)
  open import Data.Sum
    using (_⊎_ ; inj₁ ; inj₂ ; [_,_]′)
  open import Function using (_∘_)

  module Presheaf where
  {- Machinery for interpretations -}

    record 𝒫 : Set₁ where
      field
        In   : Ctx → Set
        Wken : ∀ {Δ Γ} (Γ⊆Δ : Γ ⊆ Δ) → (In Δ → In Γ)

    open 𝒫

    -- natural transformation
    _→∙_ : 𝒫 → 𝒫 → Set
    (P →∙ Q) = ∀ {Γ} → P .In Γ → Q .In Γ

    _×ᴾ_ : 𝒫 → 𝒫 → 𝒫
    In (P ×ᴾ Q) Γ                 = (In P Γ) × (In Q Γ)
    Wken (P ×ᴾ Q) Γ⊆Δ (fst , snd) = (Wken P Γ⊆Δ fst) , (Wken Q Γ⊆Δ snd)

    _⇒ᴾ_ :  𝒫 → 𝒫 → 𝒫
    In (P ⇒ᴾ Q) Γ             = ∀ {Δ} → Δ ⊆ Γ → P .In Δ → Q .In Δ
    (P ⇒ᴾ Q) .Wken Γ⊆Δ₁ f Δ⊆Γ = f (⊆-trans Δ⊆Γ  Γ⊆Δ₁)

    _+ᴾ_ :  𝒫 → 𝒫 → 𝒫
    In (P +ᴾ Q) Γ    = (In P Γ) ⊎ (In Q Γ)
    (P +ᴾ Q) .Wken Γ⊆Δ = [ inj₁ ∘ Wken P Γ⊆Δ , inj₂ ∘ Wken Q Γ⊆Δ  ]′ 

    𝟙ᴾ : 𝒫
    𝟙ᴾ = record { In = λ _ → ⊤ ; Wken = λ {Δ} {Γ} Γ⊆Δ _ → tt }

  open Presheaf
  open 𝒫

  module CoverMonad where

    data 𝒞 (A : 𝒫) (ℓ : Label) : Ctx → Set where
      return : ∀ {Γ}       → A .In Γ → 𝒞 A ℓ Γ
      bind   : ∀ {Γ} {a}   → Ne (〈 a 〉 ℓ) Γ → 𝒞 A ℓ (Γ `, a) → 𝒞 A ℓ Γ
      branch : ∀ {Γ} {a b} → Ne (a + b) Γ →  𝒞 A ℓ (Γ `, a) →  𝒞 A ℓ (Γ `, b) → 𝒞 A ℓ Γ

    wken𝒞 : ∀ {ℓ} {A} {Γ Δ} → Γ ⊆ Δ → 𝒞 A ℓ Δ → 𝒞 A ℓ Γ
    wken𝒞 {A = A} e (return x) = return (Wken A e x)
    wken𝒞 e (bind x m)         = bind   (wkenNe e x) (wken𝒞 (keep e) m)
    wken𝒞 e (branch x m₁ m₂)    = branch (wkenNe e x) (wken𝒞 (keep e) m₁) (wken𝒞 (keep e) m₂)

    {- The cover monad is a presheaf -}
    𝒞ᴾ : Label → 𝒫 → 𝒫
    𝒞ᴾ ℓ A = record { In = 𝒞 A ℓ ; Wken = wken𝒞 }

    {- We can implement functorial map -}
    map𝒞  : ∀ {ℓ} {A B} → (A →∙ B) → (𝒞ᴾ ℓ A →∙ 𝒞ᴾ ℓ B)
    map𝒞 f (return x) = return (f x)
    map𝒞 f (bind x m) = bind x (map𝒞 f m)
    map𝒞 f (branch x c₁ c₂) = branch x (map𝒞 f c₁) (map𝒞 f c₂)

    {- And derive μ -}
    join𝒞 : ∀ {ℓ} {A} → 𝒞ᴾ ℓ (𝒞ᴾ ℓ A) →∙ 𝒞ᴾ ℓ A
    join𝒞 (return x) = x
    join𝒞 (bind f m) = bind f (join𝒞 m)
    join𝒞 (branch x c₁ c₂) = branch x (join𝒞 c₁) (join𝒞 c₂)

    mapExp𝒞  : ∀ {ℓ} {A B} → (A ⇒ᴾ B) →∙ (𝒞ᴾ ℓ A ⇒ᴾ 𝒞ᴾ ℓ B)
    mapExp𝒞 f e (return x) = return (f e x)
    mapExp𝒞 f e (bind x m) = bind x (mapExp𝒞 f (drop e) m)
    mapExp𝒞 f e (branch x c₁ c₂) = branch x (mapExp𝒞 f (drop e) c₁) (mapExp𝒞 f (drop e) c₂)

    bindExp𝒞 : ∀ {ℓ} {A B} → (A ⇒ᴾ 𝒞ᴾ ℓ B) →∙ (𝒞ᴾ ℓ A ⇒ᴾ 𝒞ᴾ ℓ B)
    bindExp𝒞 f e m = join𝒞 (mapExp𝒞 f e m)

    up𝒞 : ∀ {ℓᴸ ℓᴴ} {A} → ℓᴸ ⊑ ℓᴴ → (𝒞ᴾ ℓᴸ A →∙ 𝒞ᴾ ℓᴴ A)
    up𝒞 L⊑H (return x)  = return x
    up𝒞 L⊑H (bind n k)  = bind (L⊑H ↑ n) (up𝒞 L⊑H k)
    up𝒞 L⊑H (branch x c₁ c₂) = branch x (up𝒞 L⊑H c₁) (up𝒞 L⊑H c₂)

  open CoverMonad public

  -- decision monad for coproducts
  module DecMonad where

  data 𝒟 (A : 𝒫) : Ctx → Set where
    return : ∀ {Γ} → A .In Γ → 𝒟 A Γ
    branch : ∀ {Γ} {a b}
      → Ne (a + b) Γ
      → (c₁ : 𝒟 A (Γ `, a)) → (c₂ :  𝒟 A (Γ `, b))
      ---------------------------------------------
      → 𝒟 A Γ

  wken𝒟 : ∀ {A} {Γ Δ} → Γ ⊆ Δ → 𝒟 A Δ → 𝒟 A Γ
  wken𝒟 {A} e (return x) = return (Wken A e x)
  wken𝒟 e (branch x c₁ c₂) = branch (wkenNe e x) (wken𝒟 (keep e) c₁) (wken𝒟 (keep e) c₂)
    
  𝒟ᴾ : 𝒫 → 𝒫
  𝒟ᴾ A = record { In = 𝒟 A ; Wken = wken𝒟 }

  map𝒟  : ∀ {A B} → (A →∙ B) → (𝒟ᴾ A →∙ 𝒟ᴾ B)
  map𝒟 f (return x) = return (f x)
  map𝒟 f (branch x c₁ c₂) = branch x (map𝒟 f c₁) (map𝒟 f c₂)

  join𝒟 : ∀ {A} → 𝒟ᴾ (𝒟ᴾ A) →∙ 𝒟ᴾ A
  join𝒟 (return x) = x
  join𝒟 (branch x m m₁) = branch x (join𝒟 m) (join𝒟 m₁)

  mapExp𝒟  : ∀ {A B} → (A ⇒ᴾ B) →∙ (𝒟ᴾ A ⇒ᴾ 𝒟ᴾ B)
  mapExp𝒟 f e (return x) =
    return (f e x)
  mapExp𝒟 f e (branch x c₁ c₂) =
    branch x (mapExp𝒟 f (drop e) c₁) (mapExp𝒟 f (drop e) c₂)

  bindExp𝒟 : ∀ {A B} → (A ⇒ᴾ 𝒟ᴾ B) →∙ (𝒟ᴾ A ⇒ᴾ 𝒟ᴾ B)
  bindExp𝒟 f e m = join𝒟 (mapExp𝒟 f e m)

--  ap𝒟 : 
  open DecMonad

  module Interpretation where

    Termᴾ : Type → 𝒫
    Termᴾ τ = record { In = Term τ ; Wken = wkenTm }

    Nfᴾ : Type → 𝒫
    Nfᴾ τ = record { In = Nf τ ; Wken = wkenNf }

    Neᴾ : Type → 𝒫
    Neᴾ τ = record { In = Ne τ ; Wken = wkenNe }

    𝕓ᴾ : 𝒫
    𝕓ᴾ = record { In   = Nf 𝕓 ; Wken = wkenNf }

    ⟦_⟧ : Type → 𝒫
    ⟦ 𝟙  ⟧        = 𝟙ᴾ
    ⟦ 𝕓 ⟧         = 𝕓ᴾ
    ⟦ a ⇒ b ⟧     = ⟦ a ⟧ ⇒ᴾ  ⟦ b ⟧
    ⟦ (〈 a 〉 ℓ) ⟧  = 𝒞ᴾ ℓ ⟦ a ⟧
    ⟦ a + b ⟧     = 𝒟ᴾ (⟦ a ⟧ +ᴾ ⟦ b ⟧)

    ⟦_⟧ₑ : Ctx → 𝒫
    ⟦ Ø ⟧ₑ      = 𝟙ᴾ
    ⟦ Γ `, a ⟧ₑ = ⟦ Γ ⟧ₑ ×ᴾ ⟦ a ⟧

  open Interpretation public

  module DecMonadOps where

  run𝒟Nf : ∀ {a : Type} → 𝒟ᴾ (Nfᴾ a) →∙ (Nfᴾ a)
  run𝒟Nf (return x) = x
  run𝒟Nf (branch x m m₁) = case x (run𝒟Nf m) (run𝒟Nf m₁)
      
  run𝒟 : ∀ {a : Type} → 𝒟ᴾ ⟦ a ⟧ →∙ ⟦ a ⟧
  run𝒟 {𝟙}      _ = tt
  run𝒟 {𝕓}      m = run𝒟Nf m
  run𝒟 {a + b}  m = join𝒟 m
  run𝒟 {a ⇒ b}  m = λ e x → run𝒟 {b} (run𝒟⇒ m e (return x))
    where
    run𝒟⇒ : 𝒟ᴾ ⟦ a ⇒ b ⟧ →∙ (𝒟ᴾ ⟦ a ⟧ ⇒ᴾ 𝒟ᴾ ⟦ b ⟧)
    run𝒟⇒ (return f) e x = mapExp𝒟 f e x
    run𝒟⇒ (branch n c₁ c₂) e x =
      branch (wkenNe e n)
        (run𝒟⇒ c₁ (keep e) (wken𝒟 (drop ⊆-refl) x))
        (run𝒟⇒ c₂ (keep e) (wken𝒟 (drop ⊆-refl) x))
  run𝒟 {〈 a 〉 ℓ} m = run𝒟𝒞 m
    where
    run𝒟𝒞 : 𝒟ᴾ (𝒞ᴾ ℓ ⟦ a ⟧) →∙ (𝒞ᴾ ℓ ⟦ a ⟧)
    run𝒟𝒞 (return x) = x
    run𝒟𝒞 (branch x c₁ c₂) = branch x (run𝒟𝒞 c₁) (run𝒟𝒞 c₂)
    
  open DecMonadOps
  module NbE where

    open 𝒫

    lookup : ∀ {a Γ} → a ∈ Γ → (⟦ Γ ⟧ₑ →∙ ⟦ a ⟧)
    lookup ze     (_ , v) = v
    lookup (su v) (γ , _) = lookup v γ

    eval : ∀ {a Γ} → Term a Γ → (⟦ Γ ⟧ₑ →∙ ⟦ a ⟧)
    eval unit _ = tt
    eval {Γ = Γ} (`λ t) γ     = λ e u → eval t (Wken ⟦ Γ ⟧ₑ e γ , u)
    eval (var x) γ            = lookup x γ
    eval (t ∙ u) γ            = (eval t γ) ⊆-refl (eval u γ)
    eval (η t) γ              = return (eval t γ)
    eval {Γ = Γ} (t ≫= m) γ  = bindExp𝒞 (λ e a → eval m (Wken ⟦ Γ ⟧ₑ e γ , a)) ⊆-refl (eval t γ)
    eval (c ↑ t) γ            = up𝒞 c (eval t γ)
    eval (inl t) γ            = return (inj₁ (eval t γ))
    eval (inr t) γ            = return (inj₂ (eval t γ))
    eval {a} {Γ} (case {_} {b} {c} t t₁ t₂) {Δ} γ =
      run𝒟 {a} (mapExp𝒟 match ⊆-refl (eval t γ))
      where
      match : ((⟦ b ⟧ +ᴾ ⟦ c ⟧) ⇒ᴾ ⟦ a ⟧) .In Δ
      match e (inj₁ x) = eval t₁ ((Wken ⟦ Γ ⟧ₑ e γ) , x)
      match e (inj₂ y) = eval t₂ ((Wken ⟦ Γ ⟧ₑ e γ) , y)

    mutual

      reifyVal : ∀ {a} → ⟦ a ⟧ →∙ Nfᴾ a
      reifyVal {𝟙} x      = unit
      reifyVal {𝕓} x      = x
      reifyVal {a ⇒ b} f  = `λ (reifyVal (f (drop ⊆-refl) (reflect {a} (var ze))))
      reifyVal {〈 a 〉 ℓ} m = reifyVal𝒞 m
      reifyVal {a + b}  m = run𝒟Nf (map𝒟 reifySum m)
      
      reifyVal𝒟 : ∀ {a} → 𝒟ᴾ ⟦ a ⟧ →∙ Nfᴾ a
      reifyVal𝒟 {a} m = run𝒟Nf {a} (map𝒟 reifyVal m) 

      reifySum : ∀ {a b} → (⟦ a ⟧ +ᴾ ⟦ b ⟧) →∙ Nfᴾ (a + b)
      reifySum {a} {b} = [ inl ∘ reifyVal {a} , inr ∘ reifyVal {b} ]′
      
      reifyVal𝒞 : ∀ {a} {ℓ} → 𝒞ᴾ ℓ ⟦ a ⟧ →∙ Nfᴾ (〈 a 〉 ℓ)
      reifyVal𝒞 (return x) = η (reifyVal x)
      reifyVal𝒞 (bind x m) = x ≫= reifyVal𝒞 m
      reifyVal𝒞 (branch x c₁ c₂) = case x (reifyVal𝒞 c₁) (reifyVal𝒞 c₂)
      
      reflect : ∀ {a} → Neᴾ a →∙ ⟦ a ⟧
      reflect {𝟙}      n = tt
      reflect {𝕓}      n = 𝕓 n
      reflect {a ⇒ b}  n = λ e v → reflect ((wkenNe e n) ∙ (reifyVal v))
      reflect {〈 a 〉 ℓ} n =  bind n (return (reflect {a} (var ze)))
      reflect {a + b}  n =
        branch n
          (return (inj₁ (reflect {a} (var ze))))
          (return (inj₂ (reflect {b} (var ze))))   

      idSubst :  ∀ Γ → ⟦ Γ ⟧ₑ .In Γ
      idSubst Ø        = tt
      idSubst (Γ `, T) = Wken ⟦ Γ ⟧ₑ (drop ⊆-refl) (idSubst Γ) , reflect {T} (var ze)

      reify : ∀{a Γ} → (⟦ Γ ⟧ₑ →∙ ⟦ a ⟧) → Nf a Γ
      reify {a} {Γ} f = reifyVal (f (idSubst Γ))

      norm : ∀ {a} → Termᴾ a →∙ Nfᴾ a
      norm t = reify (eval t)

  open NbE public

  module NI where
  
    -- ℓ ⊣ a to be read as: the type a is protected at label ℓ
    -- this definition is straight from DCC (except prot𝕓)
    data _⊣_ : Type → Label → Set where
      prot⇒ : ∀ {ℓ} {a b}    → b ⊣ ℓ  → (a ⇒ b) ⊣ ℓ
      flows : ∀ {ℓ} {a} {ℓ'} → ℓ ⊑ ℓ' → (〈 a 〉 ℓ') ⊣ ℓ
      layer : ∀ {ℓ} {a} {ℓ'} → a ⊣ ℓ  → (〈 a 〉 ℓ') ⊣ ℓ

    postulate
      -- obviously holds, remove later
      ⊑-trans : RB.Transitive _⊑_
      ⊑-dec  : RB.Decidable _⊑_
      ⊑-refl : RB.Reflexive _⊑_

    -- a labelled type is protected at a level ℓ even if its sensitivity is raised
    ≼-up : ∀ {ℓ ℓᴸ ℓᴴ} {a} → (〈 a 〉 ℓᴸ) ⊣ ℓ → ℓᴸ ⊑ ℓᴴ → (〈 a 〉 ℓᴴ) ⊣ ℓ
    ≼-up (flows p) q = flows (⊑-trans p q)
    ≼-up (layer p) q = layer p

    -- if a function is protected at a level ℓ,
    -- then its result is also protected at ℓ
    ≼-res⇒ : ∀ {ℓ} {a b} → (a ⇒ b) ⊣ ℓ → b ⊣ ℓ
    ≼-res⇒ (prot⇒ e) = e


    -- labelled context (or context protected at ℓ)
    data _⊣ᶜ_ : Ctx → Label → Set where
      Ø    : ∀ {ℓ} → Ø ⊣ᶜ ℓ
      _`,_ : ∀ {ℓ} {Γ} {a} → Γ ⊣ᶜ ℓ → a ⊣ ℓ → (Γ `, a) ⊣ᶜ ℓ

    -- first order type
    data Ground : Type → Set where
      𝟙   : Ground 𝟙
      𝕓   : Ground 𝕓
      〈_〉_ : ∀ {a} → Ground a → (ℓ : Label) → Ground (〈 a 〉 ℓ)
      _+_ : ∀ {a b} → Ground a → Ground b → Ground (a + b)

    -- 
    data Neg : Type → Set where
      𝟙    : Neg 𝟙
      𝕓    : Neg 𝕓
      ⟨_⟩_ : ∀ a → (ℓ : Label) → Neg (〈 a 〉 ℓ)
    
    -- given a context protected at ℓ,
    -- variables produce values protected at ℓ
    -- i.e., variables protect secrets
    Var-Prot : ∀ {Γ} {a} {ℓ} → Γ ⊣ᶜ ℓ → a ∈ Γ → a ⊣ ℓ
    Var-Prot (e `, a) ze = a
    Var-Prot (e `, a) (su v) = Var-Prot e v

    mutual

      -- neutral forms protect secrets
      Ne-Prot : ∀ {Γ} {a} {ℓ} → Γ ⊣ᶜ ℓ → Ne a Γ → a ⊣ ℓ
      Ne-Prot e (var x) = Var-Prot e x
      Ne-Prot e (x ∙ n) = ≼-res⇒ (Ne-Prot e x)
      Ne-Prot e (p ↑ x) = ≼-up (Ne-Prot e x) p

      -- normal forms (of first order types) protect secrets
      Nf-Prot : ∀ {Γ} {a} {ℓ} → Γ ⊣ᶜ ℓ → Neg a → Ground a → Nf a Γ → a ⊣ ℓ
      Nf-Prot e p g  unit    = {!!}
      Nf-Prot e p () (`λ n)
      Nf-Prot e p g (𝕓 x)    = Ne-Prot e x
      Nf-Prot e (⟨ a ⟩ .ℓ) (〈 g 〉 ℓ) (η n) = layer (Nf-Prot e {!!} g n)
      Nf-Prot e p g (x ≫= n) with Ne-Prot e x
      Nf-Prot e p g (x ≫= n) | flows q = flows q
      Nf-Prot e p g (x ≫= n) | layer q with Nf-Prot (e `, q) p g n
      Nf-Prot e p g (x ≫= n) | layer q | flows r = flows r
      Nf-Prot e p g (x ≫= n) | layer q | layer r = layer r
      Nf-Prot e () g (inl n)
      Nf-Prot e () g (inr n)
      Nf-Prot e p g (case x t t₁) with Ne-Prot e x
      Nf-Prot e p g (case x t t₁) | ()

    open import Data.Empty
    open import Relation.Nullary

    {-
    ⊣-dec : RB.Decidable _⊣_
    ⊣-dec 𝕓 ℓ = no (λ ())
    ⊣-dec (a ⇒ b) ℓ  with ⊣-dec b ℓ
    ⊣-dec (a ⇒ b) ℓ | yes p = yes (prot⇒ p)
    ⊣-dec (a ⇒ b) ℓ | no ¬p = no (λ {(prot⇒ x) → ¬p x})
    ⊣-dec (〈 a 〉 ℓ′) ℓ with ⊑-dec ℓ ℓ′
    ⊣-dec (〈 a 〉 ℓ′) ℓ | yes p = yes (flows p)
    ⊣-dec (〈 a 〉 ℓ′) ℓ | no ¬p with ⊣-dec a ℓ
    ⊣-dec (〈 a 〉 ℓ′) ℓ | no ¬p | yes p = yes (layer p)
    ⊣-dec (〈 a 〉 ℓ′) ℓ | no ¬p | no ¬q = no (λ { (flows x) → ¬p x ; (layer x) → ¬q x})

    ⊣ᶜ-dec : RB.Decidable _⊣ᶜ_
    ⊣ᶜ-dec Ø ℓ = yes Ø
    ⊣ᶜ-dec (Γ `, a) ℓ with ⊣-dec a ℓ
    ⊣ᶜ-dec (Γ `, a) ℓ | yes p
      with ⊣ᶜ-dec Γ ℓ
    ⊣ᶜ-dec (Γ `, a) ℓ | yes p | yes q = yes (q `, p)
    ⊣ᶜ-dec (Γ `, a) ℓ | yes p | no ¬q = no (λ {(Γ `, p) → ¬q Γ})
    ⊣ᶜ-dec (Γ `, a) ℓ | no ¬p = no (λ { (Γ `, p) → ¬p p})
    -}
        
  open NI public

  module Neutrality where

    open import Data.Empty
    open import Relation.Nullary
    
    emptyNe : ∀ {a} → ¬ (Ne a Ø)
    emptyNe (var ())
    emptyNe (x ∙ _) = emptyNe x
    emptyNe (x ↑ n) = emptyNe n

  open Neutrality public
  
