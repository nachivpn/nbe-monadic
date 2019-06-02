{-# OPTIONS --exact-split #-}

open import Level using (_⊔_)
open import Algebra.Ordered using (Promonoid)
import Data.List.Relation.Binary.Sublist.Setoid as Sublist
open import Data.List.Relation.Unary.Any using (Any)
open import Relation.Binary using (Preorder)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

-- Typed terms and subtyping coercions are parametrized by
--
--  * a preordered set of base types,
--  * a preordered monoid of effects.
--
-- These two preorders generate the subtyping relation.

module Bidirectional {c ℓ₁ ℓ₂}
                     (Base    : Preorder c ℓ₁ ℓ₂)
                     (Effects : Promonoid c ℓ₁ ℓ₂)
                     where

open import Types      Base Effects
open import Coercions  Base Effects
open import Terms      Base Effects
open import Presheaves Base Effects

open PSh

infix 4 _<!_ _≪!_

-- Declarative subtyping is a binary relation over types.
--
-- Alternative interpretation: the intrinsically typed syntax of
-- subtyping coercions `α : a <! b` between types `a` and `b`.

data _<!_ : Tp → Tp → Set (c ⊔ ℓ₂) where

  coe : ∀ {i j}
      → i ≤ j
        ------------
      → bs i <! bs j

         ------------
  unit : unit <! unit


  _⇒_ : ∀ {a₁ a₂ b₁ b₂}
      → a₂ <! a₁
      → b₁ <! b₂
        ------------------
      → a₁ ⇒ b₁ <! a₂ ⇒ b₂
 
  _𝕩_ : ∀ {a₁ a₂ b₁ b₂}
      → a₁ <! a₂
      → b₁ <! b₂
        ------------------
      → a₁ 𝕩 b₁ <! a₂ 𝕩 b₂

  ⟨_⟩_ : ∀ {e₁ e₂ a₁ a₂}
       → e₁ ⊑ e₂
       → a₁ <! a₂
         ----------------------
       → ⟨ e₁ ⟩ a₁ <! ⟨ e₂ ⟩ a₂


-- Algorithmic subtyping lifted pointwise to contexts and combined
-- with OPEs
--
-- Alternative interpretation: the intrinsically typed syntax of
-- context morphisms `Φ : Γ ≪! Δ` between contexts `Γ` and `Δ`.

data _≪!_ : Ctx → Ctx → Set (c ⊔ ℓ₂) where

       ---------
  [] : [] ≪! []
  
  _∷_ : ∀ {a b Γ Δ}
      → a <! b
      → Γ ≪! Δ
        ---------------
      → a ∷ Γ ≪! b ∷ Δ

  _∷ˡ_ : ∀ a {Γ Δ}
       → Γ ≪! Δ
         -----------
       → a ∷ Γ ≪! Δ

-- Admissible order-theoretic rules: reflexivity and transitivity
--
-- Though it is easy to prove reflexivity and transitivity admissible
-- for this very simple algorithmic subtyping relation, this can be
-- hard in general, especially for transitivity.  This is sometimes
-- referred to as the "transitivity elimination" problem.

<!-refl : ∀ {a}
        → a <! a
<!-refl {bs i}    = coe Bs.refl
<!-refl {unit}    = unit
<!-refl {a 𝕩 b}   = <!-refl 𝕩 <!-refl
<!-refl {a ⇒ b}   = <!-refl ⇒ <!-refl
<!-refl {⟨ e ⟩ a} = ⟨ Eff.refl ⟩ <!-refl

≪!-refl : ∀ {Γ}
         → Γ ≪! Γ
≪!-refl {[]}    = []
≪!-refl {a ∷ Γ} = <!-refl ∷ ≪!-refl

<!-trans : ∀ {a b c}
         → a <! b
         → b <! c
         --------
         → a <! c
<!-trans (coe i≤j)  (coe j≤k)  = coe (Bs.trans i≤j j≤k)
<!-trans unit       unit       = unit
<!-trans (α₁ ⇒ β₁)  (α₂ ⇒ β₂)  = <!-trans α₂ α₁ ⇒ <!-trans β₁ β₂
<!-trans (α₁ 𝕩 β₁)  (α₂ 𝕩 β₂)  = <!-trans α₁ α₂ 𝕩 <!-trans β₁ β₂
<!-trans (⟨ e₁⊑e₂ ⟩ α₁) (⟨ e₂⊑e₃ ⟩ α₂) =
  ⟨ Eff.trans e₁⊑e₂ e₂⊑e₃ ⟩ <!-trans α₁ α₂

≪!-trans : ∀ {Γ Δ E}
          → Γ ≪! Δ
          → Δ ≪! E
          --------
          → Γ ≪! E
≪!-trans []        []        = []
≪!-trans (α₁ ∷ Φ₁) (α₂ ∷ Φ₂) = <!-trans α₁ α₂ ∷ ≪!-trans Φ₁ Φ₂
≪!-trans (α₁ ∷ Φ₁) (a ∷ˡ Φ₂) = _ ∷ˡ ≪!-trans Φ₁ Φ₂
≪!-trans (a ∷ˡ Φ₁) Φ₂        = a ∷ˡ ≪!-trans Φ₁ Φ₂

-- Equivalence of declarative and algorithmic subtyping

<!-sound : ∀ {a b} → a <! b → a <: b
<!-sound (coe ι)   = coe ι
<!-sound unit      = unit
<!-sound (α ⇒ β)   = <!-sound α ⇒ <!-sound β
<!-sound (α 𝕩 β)   = <!-sound α 𝕩 <!-sound β
<!-sound (⟨ φ ⟩ α) = ⟨ φ ⟩ <!-sound α

<!-complete : ∀ {a b} → a <: b → a <! b
<!-complete (coe ι)     = coe ι
<!-complete unit        = unit
<!-complete (α ⇒ β)     = <!-complete α ⇒ <!-complete β
<!-complete (α 𝕩 β)     = <!-complete α 𝕩 <!-complete β
<!-complete (⟨ φ ⟩ α)   = ⟨ φ ⟩ <!-complete α
<!-complete refl        = <!-refl
<!-complete (trans α β) = <!-trans (<!-complete α) (<!-complete β)

infixr 8 _·_ _*_
infix  4 _⇇_ _⇉_ _⇇_⇉_
infixr 4 _,_
infixr 2 _∋_

-- The syntax of intrinsically *bidirectionally* typed terms

mutual

  -- Checked pure terms (mostly introduction forms)

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
 
    _*_ : ∀ {a b}
        → a <! b
        → Γ ⇉ a
        -------- (subsumption)
        → Γ ⇇ b

    up : ∀ {e f a}
       → e ⊑ f
       → Γ ⇇ a ⇉ e
         ----------- (computation)
       → Γ ⇇ ⟨ f ⟩ a


  -- Computations with checked types and inferred effect 

  data _⇇_⇉_ (Γ : Ctx) : Tp → Eff → Set (c ⊔ ℓ₂) where

    ◇ : ∀ {a}
      → Γ ⇇ a
        --------- (monadic unit/return/diamond)
      → Γ ⇇ a ⇉ ε

    _>>=_ : ∀ {e f a b}
          → Γ ⇉ ⟨ e ⟩ a
          → a ∷ Γ ⇇ b ⇉ f
            ------------- (monadic bind/Kleisli extension)
          → Γ ⇇ b ⇉ f ∙ e


  -- Terms and computations with syntesized types
  -- (mostly elimination forms)

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


-- Alternative versions of variable, elimination and computaion typing
-- used in the equivalence proof below.

infix 4 _∈'_ _⇇'_ _⇇⟨_⟩_

data _∈'_ : Tp → Ctx → Set (c ⊔ ℓ₂) where
  _*_ : ∀ {a b Γ} → a <! b → a ∈ Γ → b ∈' Γ

here' : ∀ {a b Γ} → a <! b → b ∈' (a ∷ Γ)
here' α = α * here refl

there' : ∀ {a b Γ} → a ∈' Γ → a ∈' (b ∷ Γ)
there' (α * x) = α * there x

≪!-lookup : ∀ {a Γ Δ} → Γ ≪! Δ → a ∈ Δ → a ∈' Γ
≪!-lookup (a ∷ˡ Φ) x           = there' (≪!-lookup Φ x)
≪!-lookup (α ∷ Φ)  (here refl) = α * (here refl)
≪!-lookup (α ∷ Φ)  (there x)   = there' (≪!-lookup Φ x)

data _⇇'_ (Γ : Ctx) : Tp → Set (c ⊔ ℓ₂) where
  _*_ : ∀ {a b} → a <! b → Γ ⇉ a → Γ ⇇' b

var' : ∀ {Γ a} → a ∈' Γ → Γ ⇇' a
var' (α * x) = α * (var x)

fst' : ∀ {Γ a b} → Γ ⇇' a 𝕩 b → Γ ⇇' a
fst' ((α 𝕩 β) * t) = α * fst t

snd' : ∀ {Γ a b} → Γ ⇇' a 𝕩 b → Γ ⇇' b
snd' ((α 𝕩 β) * t) = β * snd t

injectSyn : ∀ {Γ a} → Γ ⇇' a → Γ ⇇ a
injectSyn (α * t)  = α * t

data _⇇⟨_⟩_ (Γ : Ctx) : Eff → Tp → Set (c ⊔ ℓ₂) where
  up  : ∀ {a e f} → e ⊑ f → Γ ⇇ a ⇉ e → Γ ⇇⟨ f ⟩ a

injectCmp : ∀ {Γ a e} → Γ ⇇⟨ e ⟩ a → Γ ⇇ ⟨ e ⟩ a
injectCmp (up φ t) = up φ t

-- Context narrowing/monotonicity is admissible for variables.

narrowVar : ∀ {a Γ Δ} → Γ ≪! Δ → a ∈' Δ → a ∈' Γ
narrowVar Φ (α * x) with ≪!-lookup Φ x
... | β * y = <!-trans β α * y

-- A combined proof of admissibility of subsumption and context
-- narrowing/monotonicity for bidirectionally typed terms.

mutual

  narCoeChk : ∀ {a b Γ Δ} → Γ ≪! Δ → Δ ⇇ a → a <! b → Γ ⇇ b
  narCoeChk Φ ⟨⟩       unit      = ⟨⟩
  narCoeChk Φ (t , u)  (α 𝕩 β)   = narCoeChk Φ t α , narCoeChk Φ u β
  narCoeChk Φ (ƛ t)    (α ⇒ β)   = ƛ (narCoeChk (α ∷ Φ) t β)
  narCoeChk Φ (β * t)  α         = injectSyn (narCoeSyn Φ t (<!-trans β α))
  narCoeChk Φ (up φ t) (⟨ ψ ⟩ α) = injectCmp (narCoeCmp Φ t α (Eff.trans φ ψ))
  
  narCoeCmp : ∀ {a b e f Γ Δ} →
              Γ ≪! Δ → Δ ⇇ a ⇉ e → a <! b → e ⊑ f → Γ ⇇⟨ f ⟩ b
  narCoeCmp Φ (◇ t)     α φ = up φ (◇ (narCoeChk Φ t α))
  narCoeCmp Φ (t >>= u) α φ with narCoeSyn Φ t <!-refl
  ... | (⟨ ψ ⟩ β) * t'      with narCoeCmp (β ∷ Φ) u α Eff.refl
  ... | up φ' u' = up (Eff.trans (Eff.monotonic φ' ψ) φ) (t' >>= u')

  narCoeSyn : ∀ {a b Γ Δ} → Γ ≪! Δ → Δ ⇉ a → a <! b → Γ ⇇' b
  narCoeSyn Φ (var x) α = var' (narrowVar Φ (α * x))
  narCoeSyn Φ (fst t) α = fst' (narCoeSyn Φ t (α 𝕩 <!-refl))
  narCoeSyn Φ (snd t) α = snd' (narCoeSyn Φ t (<!-refl 𝕩 α))
  narCoeSyn Φ (t · u) α with narCoeSyn Φ t <!-refl
  ... | (α' ⇒ β) * t' = <!-trans β α * t' · narCoeChk Φ u α'
  narCoeSyn Φ (a ∋ t) α = α * (a ∋ narCoeChk Φ t <!-refl)

-- Subsumption of checked terms is admissible

_*'_ : ∀ {a b Γ} → a <! b → Γ ⇇ a → Γ ⇇ b
α *' t = narCoeChk ≪!-refl t α

-- Some admissible elimination rules
--
-- NOTE/FIXME: these perform some reductions and/or introduce
-- ascriptions.  To avoid this kind of issue, declarative syntax would
-- have to be divided into intro-forms and eliminations as well...

fstChk : ∀ {Γ a b} → Γ ⇇ a 𝕩 b → Γ ⇇ a
fstChk (t , u)       = t
fstChk ((α 𝕩 β) * t) = α * (fst t)

sndChk : ∀ {Γ a b} → Γ ⇇ a 𝕩 b → Γ ⇇ b
sndChk (t , u)       = u
sndChk ((α 𝕩 β) * t) = β * (snd t)

appChk : ∀ {Γ a b} → Γ ⇇ a ⇒ b → Γ ⇇ a → Γ ⇇ b
appChk (ƛ t)         u = <!-refl * ((_ ∋ ƛ t) · u)
appChk ((α ⇒ β) * t) u = β * (t · (α *' u))

-- FIXME: finish this

bindChk : ∀ {Γ e f a b} → Γ ⇇ ⟨ e ⟩ a → a ∷ Γ ⇇ ⟨ f ⟩ b → Γ ⇇ ⟨ f ∙ e ⟩ b
bindChk t u = {!!}

-- Equivalence of declarative and bidirectional typing
--
-- FIXME: finish this.

mutual

  soundChk : ∀ {Γ a} → Γ ⇇ a → Γ ⊢ a
  soundChk t = {!!}

  soundCmp : ∀ {Γ a e} → Γ ⇇ a ⇉ e → Γ ⊢ ⟨ e ⟩ a
  soundCmp t = {!!}

  soundSyn : ∀ {Γ a} → Γ ⇉ a → Γ ⊢ a
  soundSyn t = {!!}

complete : ∀ {Γ a} → Γ ⊢ a → Γ ⇇ a
complete (var x)   = <!-refl * var x
complete ⟨⟩        = ⟨⟩
complete (t , u)   = complete t , complete u
complete (fst t)   = fstChk (complete t)
complete (snd t)   = sndChk (complete t)
complete (ƛ t)     = ƛ (complete t)
complete (t · u)   = appChk (complete t) (complete u)
complete (◇ t)     = up Eff.refl (◇ (complete t))
complete (t >>= u) = {!!}
complete (α * t)   = (<!-complete α) *' (complete t)
complete (a ∋ t)   = <!-refl * (a ∋ (complete t))


