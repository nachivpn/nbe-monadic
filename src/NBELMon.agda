open import Relation.Binary.Lattice
open import Level

module NBELMon (JSL : JoinSemilattice 0ℓ 0ℓ 0ℓ)where

  import Relation.Binary as B

  Label = JoinSemilattice.Carrier JSL
  _⊑_   = JoinSemilattice._≤_ JSL

  module Type where

    -- Types are either function space and
    -- a base type for every i ∈ I
    data Type  : Set where
      𝕓     :                 Type
      _⇒_   : (a b : Type)  → Type
      〈_〉_   : (a : Type) (ℓ : Label) → Type
 
    infixr 10 _⇒_

    -- Ctx as a snoc list of types
    data Ctx : Set where
      Ø    : Ctx
      _`,_ : Ctx → Type → Ctx

  open Type

  module Weakening where

    -- Weakening over contexts Γ ⊆ Δ to be read as:
    -- Γ is weaker (contains possibly more types) than Δ
    -- Δ is thinner (contains possibly less types) than Γ
    data _⊆_ : Ctx → Ctx → Set where
      base : Ø ⊆ Ø
      keep : ∀ {T Γ Δ} → Γ ⊆ Δ → (Γ `, T) ⊆ (Δ `, T)
      drop : ∀ {T Γ Δ} → Γ ⊆ Δ → (Γ `, T) ⊆ Δ

    -- Weakenings are a preorder relation
    ⊆-refl : B.Reflexive _⊆_
    ⊆-refl {Ø}      = base
    ⊆-refl {Γ `, T} = keep ⊆-refl

    ⊆-trans : B.Transitive _⊆_
    ⊆-trans base q = q
    ⊆-trans (keep p) (keep q) = keep (⊆-trans p q)
    ⊆-trans (keep p) (drop q) = drop (⊆-trans p q)
    ⊆-trans (drop p) q        = drop (⊆-trans p q)

  open Weakening

  module Variable where

    -- De Bruijn index into a context
    data _∈_ : Type → Ctx → Set where
      ze : ∀ {Γ a}   → a ∈ (Γ `, a)
      su : ∀ {Γ a S} → a ∈ Γ → a ∈ (Γ `, S)

    wkenⱽ : ∀ {a} {Γ Δ} → Γ ⊆ Δ → a ∈ Δ → a ∈ Γ
    wkenⱽ (keep e) ze     = ze
    wkenⱽ (keep e) (su v) = su (wkenⱽ e v)
    wkenⱽ (drop e) v      = su (wkenⱽ e v)

  open Variable

  module Term where

    data Term : Type → Ctx → Set where
      `λ    : ∀ {Γ} {a b} → Term b (Γ `, a) → Term (a ⇒ b) Γ
      var   : ∀ {Γ} {a}   → a ∈ Γ → Term a Γ
      _∙_   : ∀ {Γ} {a b} → Term (a ⇒ b) Γ → Term a Γ → Term b Γ
      _↑_   : ∀ {ℓᴸ ℓᴴ} {Γ} {a} → ℓᴸ ⊑ ℓᴴ → Term (〈 a 〉 ℓᴸ) Γ → Term (〈 a 〉 ℓᴴ) Γ
      η     : ∀ {ℓ} {Γ} {a}    → Term a Γ → Term (〈 a 〉 ℓ) Γ
      _≫=_ : ∀ {ℓ} {Γ} {a b} → Term (〈 a 〉 ℓ) Γ → Term (〈 b 〉 ℓ) (Γ `, a) → Term (〈 b 〉 ℓ) Γ


    wkenᵀ : ∀ {a} {Γ Δ} → Γ ⊆ Δ → Term a Δ → Term a Γ
    wkenᵀ e (`λ t)     = `λ (wkenᵀ (keep e) t)
    wkenᵀ e (var x)    = var (wkenⱽ e x)
    wkenᵀ e (t ∙ t₁)   = wkenᵀ e t ∙ wkenᵀ e t₁
    wkenᵀ e (η t)      = η (wkenᵀ e t)
    wkenᵀ e (t ≫= k)  = wkenᵀ e t ≫= wkenᵀ (keep e) k
    wkenᵀ e (x ↑ t)   = x ↑ wkenᵀ e t

  open Term

  module NormalForm where

  mutual

    data Ne : Type → Ctx → Set where
      var   : ∀ {Γ} {a}   → a ∈ Γ → Ne a Γ
      _∙_   : ∀ {Γ} {a b} → Ne (a ⇒ b) Γ → Nf a Γ → Ne b Γ
      _↑_   : ∀ {ℓᴸ ℓᴴ} {Γ} {a} → ℓᴸ ⊑ ℓᴴ → Ne (〈 a 〉 ℓᴸ) Γ → Ne (〈 a 〉 ℓᴴ) Γ

    data Nf : Type → Ctx → Set where
      `λ    : ∀ {Γ} {a b}      → Nf b (Γ `, a) → Nf (a ⇒ b) Γ
      𝕓     : ∀ {Γ}            → Ne 𝕓 Γ   → Nf 𝕓 Γ
      η     : ∀ {ℓ} {Γ}  {a}   → Nf a Γ → Nf (〈 a 〉 ℓ) Γ
      _≫=_ : ∀ {ℓ} {Γ} {a b}  → Ne (〈 a 〉 ℓ) Γ → Nf (〈 b 〉 ℓ) (Γ `, a) → Nf (〈 b 〉 ℓ) Γ

    wkenNe : ∀ {T} {Γ Δ} → Γ ⊆ Δ → Ne T Δ → Ne T Γ
    wkenNe e (var x) = var (wkenⱽ e x)
    wkenNe e (n ∙ x) = (wkenNe e n) ∙ (wkenNf e x)
    wkenNe e (c ↑ n) = c ↑ wkenNe e n

    wkenNf : ∀ {T} {Γ Δ} → Γ ⊆ Δ → Nf T Δ → Nf T Γ
    wkenNf e (`λ n)    = `λ (wkenNf (keep e) n)
    wkenNf e (η m)     = η (wkenNf e m)
    wkenNf e (𝕓 n)     = 𝕓 (wkenNe e n)
    wkenNf e (x ≫= m) = (wkenNe e x) ≫= wkenNf (keep e) m

  open NormalForm

  open import Data.Product
  open import Data.Unit hiding (_≤_)

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

    _×𝒫_ : 𝒫 → 𝒫 → 𝒫
    In (P ×𝒫 Q) Γ                 = (In P Γ) × (In Q Γ)
    Wken (P ×𝒫 Q) Γ⊆Δ (fst , snd) = (Wken P Γ⊆Δ fst) , (Wken Q Γ⊆Δ snd)

    _⇒𝒫_ :  𝒫 → 𝒫 → 𝒫
    In (P ⇒𝒫 Q) Γ             = ∀ {Δ} → Δ ⊆ Γ → P .In Δ → Q .In Δ
    (P ⇒𝒫 Q) .Wken Γ⊆Δ₁ f Δ⊆Γ = f (⊆-trans Δ⊆Γ  Γ⊆Δ₁)

    𝟙𝒫 : 𝒫
    𝟙𝒫 = record { In = λ _ → ⊤ ; Wken = λ {Δ} {Γ} Γ⊆Δ _ → tt }

  open Presheaf
  open 𝒫

  module CoverMonad where

    data 𝒞 (A : 𝒫) (ℓ : Label) : Ctx → Set where
      return : ∀ {Γ}       → A .In Γ → 𝒞 A ℓ Γ
      bind   : ∀ {Γ} {a}   → Ne (〈 a 〉 ℓ) Γ → 𝒞 A ℓ (Γ `, a) → 𝒞 A ℓ Γ

    wken𝒞 : ∀ {ℓ} {A} {Γ Δ} → Γ ⊆ Δ → 𝒞 A ℓ Δ → 𝒞 A ℓ Γ
    wken𝒞 {A = A} e (return x) = return (Wken A e x)
    wken𝒞 e (bind x m)         = bind   (wkenNe e x) (wken𝒞 (keep e) m)

    {- The cover monad is a presheaf -}
    𝒞𝒫 : Label → 𝒫 → 𝒫
    𝒞𝒫 ℓ A = record { In = 𝒞 A ℓ ; Wken = wken𝒞 }

    {- We can implement functorial map -}
    map𝒞  : ∀ {ℓ} {A B} → (A →∙ B) → (𝒞𝒫 ℓ A →∙ 𝒞𝒫 ℓ B)
    map𝒞 f (return x) = return (f x)
    map𝒞 f (bind x m) = bind x (map𝒞 f m)

    {- And derive μ -}
    join𝒞 : ∀ {ℓ} {A} → 𝒞𝒫 ℓ (𝒞𝒫 ℓ A) →∙ 𝒞𝒫 ℓ A
    join𝒞 (return x) = x
    join𝒞 (bind f m) = bind f (join𝒞 m)

    mapExp𝒫  : ∀ {ℓ} {A B} → (A ⇒𝒫 B) →∙ (𝒞𝒫 ℓ A ⇒𝒫 𝒞𝒫 ℓ B)
    mapExp𝒫 f e (return x) = return (f e x)
    mapExp𝒫 f e (bind x m) = bind x (mapExp𝒫 f (drop e) m)

    bindExp𝒞′ : ∀ {ℓ} {A B} → (A ⇒𝒫 𝒞𝒫 ℓ B) →∙ (𝒞𝒫 ℓ A ⇒𝒫 𝒞𝒫 ℓ B)
    bindExp𝒞′ f e m = join𝒞 (mapExp𝒫 f e m)

    bindExp𝒞 : ∀ {ℓ} {A B} → (A ⇒𝒫 𝒞𝒫 ℓ B) →∙ (𝒞𝒫 ℓ A ⇒𝒫 𝒞𝒫 ℓ B)
    bindExp𝒞 f Δ⊆Γ (return x) = f Δ⊆Γ x
    bindExp𝒞 f Δ⊆Γ (bind x m) = bind x (bindExp𝒞 f (drop Δ⊆Γ) m)

    up𝒞 : ∀ {ℓᴸ ℓᴴ} {A} → ℓᴸ ⊑ ℓᴴ → (𝒞𝒫 ℓᴸ A →∙ 𝒞𝒫 ℓᴴ A)
    up𝒞 L⊑H (return x)  = return x
    up𝒞 L⊑H (bind n k)  = bind (L⊑H ↑ n) (up𝒞 L⊑H k)

  open CoverMonad

  module Interpretation where

    Term𝒫 : Type → 𝒫
    Term𝒫 τ = record { In = Term τ ; Wken = wkenᵀ }

    Nf𝒫 : Type → 𝒫
    Nf𝒫 τ = record { In = Nf τ ; Wken = wkenNf }

    Ne𝒫 : Type → 𝒫
    Ne𝒫 τ = record { In = Ne τ ; Wken = wkenNe }

    𝕓𝒫 : 𝒫
    𝕓𝒫 = record { In   = Nf 𝕓 ; Wken = wkenNf }

    ⟦_⟧ : Type → 𝒫
    ⟦ 𝕓 ⟧      = 𝕓𝒫
    ⟦ a ⇒ b ⟧  = ⟦ a ⟧ ⇒𝒫  ⟦ b ⟧
    ⟦ (〈 a 〉 ℓ) ⟧  = 𝒞𝒫 ℓ ⟦ a ⟧

    ⟦_⟧ₑ : Ctx → 𝒫
    ⟦ Ø ⟧ₑ      = 𝟙𝒫
    ⟦ Γ `, a ⟧ₑ = ⟦ Γ ⟧ₑ ×𝒫 ⟦ a ⟧

  open Interpretation

  module NbE where

    open 𝒫

    lookup : ∀ {a Γ} → a ∈ Γ → (⟦ Γ ⟧ₑ →∙ ⟦ a ⟧)
    lookup ze     (_ , v) = v
    lookup (su v) (γ , _) = lookup v γ

    eval : ∀ {a Γ} → Term a Γ → (⟦ Γ ⟧ₑ →∙ ⟦ a ⟧)
    eval {Γ = Γ} (`λ t) γ     = λ e u → eval t (Wken ⟦ Γ ⟧ₑ e γ , u)
    eval {Γ = Γ} (var x) γ    = lookup x γ
    eval {Γ = Γ} (t ∙ u) γ    = (eval t γ) ⊆-refl (eval u γ)
    eval {Γ = Γ} (η t) γ      = return (eval t γ)
    eval {Γ = Γ} (t ≫= m) γ  =
      bindExp𝒞 (λ e a → eval m (Wken ⟦ Γ ⟧ₑ e γ , a)) ⊆-refl (eval t γ)
    eval {Γ = Γ} (c ↑ t) γ = up𝒞 c (eval t γ)

    mutual

      reifyVal : ∀ {a} → ⟦ a ⟧ →∙ Nf𝒫 a
      reifyVal {𝕓} {Γ} x      = x
      reifyVal {a ⇒ b} {Γ} f = `λ (reifyVal (f (drop ⊆-refl) (reflect {a} (var ze))))
      reifyVal {〈 a 〉 ℓ} {Γ} (return x) = η (reifyVal x)
      reifyVal {〈 a 〉 ℓ} {Γ} (bind m k) = m ≫= (reifyVal k)

      reflect : ∀ {a} → Ne𝒫 a →∙ ⟦ a ⟧
      reflect {𝕓} {Γ} n       = 𝕓 n
      reflect {a ⇒ b} {Γ} n    = λ e v → reflect ((wkenNe e n) ∙ (reifyVal v))
      reflect {〈 a 〉 ℓ} {Γ} n  =  bind n (return (reflect {a} (var ze)))

      idSubst :  ∀ Γ → ⟦ Γ ⟧ₑ .In Γ
      idSubst Ø        = tt
      idSubst (Γ `, T) = Wken ⟦ Γ ⟧ₑ (drop ⊆-refl) (idSubst Γ) , reflect {T} (var ze)

      reify : ∀{a Γ} → (⟦ Γ ⟧ₑ →∙ ⟦ a ⟧) → Nf a Γ
      reify {a} {Γ} f = reifyVal (f (idSubst Γ))

      norm : ∀ {a} → Term𝒫 a →∙ Nf𝒫 a
      norm t = reify (eval t)

  open NbE

  module NI where
  
    -- a label ℓ "protects" a type
    -- this definition is straight from DCC (except prot𝕓)
    data _≼_ (ℓ : Label) : Type → Set where
      prot⇒ : ∀ {a b}    → ℓ ≼ b  → ℓ ≼ (a ⇒ b)
      flows : ∀ {a} {ℓ'} → ℓ ⊑ ℓ' → ℓ ≼ (〈 a 〉 ℓ')
      layer : ∀ {a} {ℓ'} → ℓ ≼ a  → ℓ ≼ (〈 a 〉 ℓ')

    postulate
      -- obviously holds, remove later
      ⊑-trans : ∀{ℓ₁ ℓ₂ ℓ₃} → ℓ₁ ⊑ ℓ₂ → ℓ₂ ⊑ ℓ₃ → ℓ₁ ⊑ ℓ₃

    -- a labelled type is protected at a level ℓ even if its sensitivity is raised
    ≼-up : ∀ {ℓ ℓᴸ ℓᴴ} {a} → ℓ ≼ (〈 a 〉 ℓᴸ) → ℓᴸ ⊑ ℓᴴ → ℓ ≼ (〈 a 〉 ℓᴴ)
    ≼-up (flows p) q = flows (⊑-trans p q)
    ≼-up (layer p) q = layer p

    -- if a function is protected at a level ℓ,
    -- then its result is also protected at ℓ
    ≼-res⇒ : ∀ {ℓ} {a b} → ℓ ≼ (a ⇒ b) → ℓ ≼ b
    ≼-res⇒ (prot⇒ e) = e

    -- labelled context (or context protected at ℓ)
    data LCtx (ℓ : Label) : Ctx → Set where
      nil  : LCtx ℓ Ø
      cons : ∀ {Γ} {a} → LCtx ℓ Γ → ℓ ≼ a → LCtx ℓ (Γ `, a)

    -- first order type
    data FO : Type → Set where
      base     : FO 𝕓
      labld : ∀ {a} {ℓ} → FO a → FO (〈 a 〉 ℓ) 

    -- given a context protected at ℓ,
    -- variables produce values protected at ℓ
    -- i.e., variables protect secrets
    Var-Prot : ∀ {Γ} {a} {ℓ} → LCtx ℓ Γ → a ∈ Γ → ℓ ≼ a
    Var-Prot (cons e x) ze = x
    Var-Prot (cons e x) (su v) = Var-Prot e v

    mutual

      -- neutral forms protect secrets
      Ne-Prot : ∀ {Γ} {a} {ℓ} → LCtx ℓ Γ → Ne a Γ → ℓ ≼ a
      Ne-Prot e (var x) = Var-Prot e x
      Ne-Prot e (x ∙ n) = ≼-res⇒ (Ne-Prot e x)
      Ne-Prot e (p ↑ x) = ≼-up (Ne-Prot e x) p

      -- normal forms (of first order types) protect secrets
      Nf-Prot : ∀ {Γ} {a} {ℓ} → LCtx ℓ Γ → FO a → Nf a Γ → ℓ ≼ a
      Nf-Prot e () (`λ n)
      Nf-Prot e r (𝕓 x)         = Ne-Prot e x
      Nf-Prot e (labld r) (η n) = layer (Nf-Prot e r n)
      Nf-Prot e r (x ≫= n) with Ne-Prot e x
      Nf-Prot e r (x ≫= n) | flows p = flows p
      Nf-Prot e r (x ≫= n) | layer p with Nf-Prot (cons e p) r n
      Nf-Prot e r (x ≫= n) | layer p | flows q = flows q
      Nf-Prot e r (x ≫= n) | layer p | layer q = layer q  
