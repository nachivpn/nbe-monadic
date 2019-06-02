------------------------------------------------------------------------
-- Algebraic structures with compatible orders
------------------------------------------------------------------------

module Algebra.Ordered where

open import Algebra
open import Algebra.FunctionProperties
open import Algebra.Structures
open import Data.Product using (proj₁; proj₂)
open import Level using (suc; _⊔_)
open import Relation.Binary
open import Relation.Binary.Lattice
import Relation.Binary.Properties.DistributiveLattice as DProps
import Relation.Binary.Properties.JoinSemilattice as JSProps
import Relation.Binary.Properties.MeetSemilattice as MSProps
import Relation.Binary.Properties.BoundedJoinSemilattice as BJSProps
import Relation.Binary.Properties.BoundedMeetSemilattice as BMSProps


------------------------------------------------------------------------
-- Preordered structures

-- Preordered semigroups (prosemigroups)

record IsProsemigroup {a ℓ₁ ℓ₂} {A : Set a}
                      (≈ : Rel A ℓ₁)
                      (∼ : Rel A ℓ₂)
                      (∙ : Op₂ A)
                      : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isSemigroup : IsSemigroup ≈ ∙
    -- Reflexivity is expressed in terms of an underlying equality:
    reflexive   : ≈ ⇒ ∼
    trans       : Transitive ∼
    monotonic   : ∙ Preserves₂ ∼ ⟶ ∼ ⟶ ∼

  open IsSemigroup isSemigroup public hiding (refl; reflexive; sym; trans)

  isPreorder : IsPreorder ≈ ∼
  isPreorder = record
    { isEquivalence = isEquivalence
    ; reflexive     = reflexive
    ; trans         = trans
    }

  open IsPreorder isPreorder public hiding (isEquivalence; reflexive; trans)

record Prosemigroup c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _∼_
  infixl 7 _∙_
  field
    Carrier        : Set c
    _≈_            : Rel Carrier ℓ₁  -- The underlying equality.
    _∼_            : Rel Carrier ℓ₂  -- The preorder.
    _∙_            : Op₂ Carrier     -- Multiplication.
    isProsemigroup : IsProsemigroup _≈_ _∼_ _∙_

  open IsProsemigroup isProsemigroup public

  preorder : Preorder c ℓ₁ ℓ₂
  preorder = record { isPreorder = isPreorder }

  semigroup : Semigroup c ℓ₁
  semigroup = record { isSemigroup = isSemigroup }

  open Semigroup semigroup public using (magma)

-- Preordered monoids (promonoids)

record IsPromonoid {a ℓ₁ ℓ₂} {A : Set a}
                   (≈ : Rel A ℓ₁)        -- The underlying equality.
                   (∼ : Rel A ℓ₂)        -- The preorder.
                   (∙ : Op₂ A) (ε : A)   -- The monoid.
                   : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isProsemigroup : IsProsemigroup ≈ ∼ ∙
    identity       : Identity ≈ ε ∙

  open IsProsemigroup isProsemigroup public

  isMonoid : IsMonoid ≈ ∙ ε
  isMonoid = record
    { isSemigroup = isSemigroup
    ; identity    = identity
    }

  open IsMonoid isMonoid public using (identityˡ; identityʳ)

record Promonoid c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _∼_
  infixl 7 _∙_
  field
    Carrier     : Set c
    _≈_         : Rel Carrier ℓ₁  -- The underlying equality.
    _∼_         : Rel Carrier ℓ₂  -- The preorder.
    _∙_         : Op₂ Carrier     -- The monoid multiplication.
    ε           : Carrier         -- The monoid unit.
    isPromonoid : IsPromonoid _≈_ _∼_ _∙_ ε

  open IsPromonoid isPromonoid public

  prosemigroup : Prosemigroup c ℓ₁ ℓ₂
  prosemigroup = record { isProsemigroup = isProsemigroup }

  open Prosemigroup prosemigroup public using (preorder; magma; semigroup)

  monoid : Monoid c ℓ₁
  monoid = record { isMonoid = isMonoid }

record IsCommutativePromonoid {a ℓ₁ ℓ₂} {A : Set a}
                              (≈ : Rel A ℓ₁) (∼ : Rel A ℓ₂)
                              (∙ : Op₂ A) (ε : A)
                              : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isProsemigroup : IsProsemigroup ≈ ∼ ∙
    identityˡ      : LeftIdentity ≈ ε ∙
    comm           : Commutative ≈ ∙

  open IsProsemigroup isProsemigroup public

  isCommutativeMonoid : IsCommutativeMonoid ≈ ∙ ε
  isCommutativeMonoid = record
    { isSemigroup = isSemigroup
    ; identityˡ   = identityˡ
    ; comm        = comm
    }

  open IsCommutativeMonoid isCommutativeMonoid public
    using (isMonoid; identity; identityʳ)

  isPromonoid : IsPromonoid ≈ ∼ ∙ ε
  isPromonoid = record
    { isProsemigroup = isProsemigroup
    ; identity       = identity
    }

record CommutativePromonoid c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _∼_
  infixl 7 _∙_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ₁  -- The underlying equality.
    _∼_     : Rel Carrier ℓ₂  -- The preorder.
    _∙_     : Op₂ Carrier     -- The monoid multiplication.
    ε       : Carrier         -- The monoid unit.
    isCommutativePromonoid : IsCommutativePromonoid _≈_ _∼_ _∙_ ε

  open IsCommutativePromonoid isCommutativePromonoid public

  promonoid : Promonoid c ℓ₁ ℓ₂
  promonoid = record { isPromonoid = isPromonoid }

  open Promonoid promonoid public
    using (preorder; magma; semigroup; monoid)

  commutativeMonoid : CommutativeMonoid c ℓ₁
  commutativeMonoid = record { isCommutativeMonoid = isCommutativeMonoid }

-- Every bounded semilattice gives rise to a commutative promonoid
--
-- FIXME: this should go into
-- Relation.Binary.Properties.BoundedJoinSemilattice.

boundedJoinSemilatticeIsPromonoid
  : ∀ {a ℓ₁ ℓ₂} → BoundedJoinSemilattice a ℓ₁ ℓ₂ → Promonoid a ℓ₁ ℓ₂
boundedJoinSemilatticeIsPromonoid boundedJoinSemilattice = record
  { Carrier = Carrier
  ; _≈_     = _≈_
  ; _∼_     = _≤_
  ; _∙_     = _∨_
  ; ε       = ⊥
  ; isPromonoid      = record
    { isProsemigroup = record
      { isSemigroup  = record
        { isMagma    = record
          { isEquivalence = isEquivalence
          ; ∙-cong        = ∨-cong
          }
        ; assoc   = ∨-assoc
        }
      ; reflexive   = reflexive
      ; trans       = trans
      ; monotonic   = ∨-monotonic
      }
    ; identity  = identity
    }
  }
  where
    open BoundedJoinSemilattice boundedJoinSemilattice
    open JSProps  joinSemilattice
    open BJSProps boundedJoinSemilattice

boundedMeetSemilatticeIsPromonoid
  : ∀ {a ℓ₁ ℓ₂} → BoundedMeetSemilattice a ℓ₁ ℓ₂ → Promonoid a ℓ₁ ℓ₂
boundedMeetSemilatticeIsPromonoid boundedMeetSemilattice = record
  { Carrier = Carrier
  ; _≈_     = _≈_
  ; _∼_     = _≤_
  ; _∙_     = _∧_
  ; ε       = ⊤
  ; isPromonoid      = record
    { isProsemigroup = record
      { isSemigroup  = record
        { isMagma    = record
          { isEquivalence = isEquivalence
          ; ∙-cong        = ∧-cong
          }
        ; assoc   = ∧-assoc
        }
      ; reflexive   = reflexive
      ; trans       = trans
      ; monotonic   = ∧-monotonic
      }
    ; identity  = identity
    }
  }
  where
    open BoundedMeetSemilattice boundedMeetSemilattice
    open MSProps  meetSemilattice
    open BMSProps boundedMeetSemilattice

-- Preordered semirings (prosemirings)

record IsProsemiring {a ℓ₁ ℓ₂} {A : Set a}
                     (≈ : Rel A ℓ₁)              -- The underlying equality.
                     (∼ : Rel A ℓ₂)              -- The preorder.
                     (+ * : Op₂ A) (0# 1# : A)   -- The semiring.
                     : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    +-isCommutativePromonoid : IsCommutativePromonoid ≈ ∼ + 0#
    *-isPromonoid            : IsPromonoid ≈ ∼ * 1#
    distrib                  : _DistributesOver_ ≈ * +
    zero                     : Zero ≈ 0# *

  distribˡ : _DistributesOverˡ_ ≈ * +
  distribˡ = proj₁ distrib

  distribʳ : _DistributesOverʳ_ ≈ * +
  distribʳ = proj₂ distrib

  zeroˡ : LeftZero ≈ 0# *
  zeroˡ = proj₁ zero

  zeroʳ : RightZero ≈ 0# *
  zeroʳ = proj₂ zero

  open IsCommutativePromonoid +-isCommutativePromonoid public
    renaming
    ( assoc       to +-assoc
    ; ∙-cong      to +-cong
    ; monotonic   to +-monotonic
    ; identity    to +-identity
    ; identityˡ   to +-identityˡ
    ; identityʳ   to +-identityʳ
    ; comm        to +-comm
    ; isMagma     to +-isMagma
    ; isSemigroup to +-isSemigroup
    ; isMonoid    to +-isMonoid
    )

  open IsPromonoid *-isPromonoid public
    using ()
    renaming
    ( assoc       to *-assoc
    ; ∙-cong      to *-cong
    ; monotonic   to *-monotonic
    ; identity    to *-identity
    ; identityˡ   to *-identityˡ
    ; identityʳ   to *-identityʳ
    ; isMagma     to *-isMagma
    ; isSemigroup to *-isSemigroup
    ; isMonoid    to *-isMonoid
    )

record Prosemiring c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _∼_
  infixl 7 _*_
  infixl 6 _+_
  field
    Carrier       : Set c
    _≈_           : Rel Carrier ℓ₁
    _∼_           : Rel Carrier ℓ₂
    _+_           : Op₂ Carrier
    _*_           : Op₂ Carrier
    0#            : Carrier
    1#            : Carrier
    isProsemiring : IsProsemiring _≈_ _∼_ _+_ _*_ 0# 1#

  open IsProsemiring isProsemiring public

  +-commutativePromonoid : CommutativePromonoid c ℓ₁ ℓ₂
  +-commutativePromonoid = record
    { isCommutativePromonoid = +-isCommutativePromonoid }

  open CommutativePromonoid +-commutativePromonoid public
    using (preorder)
    renaming
    ( magma     to +-magma
    ; semigroup to +-semigroup
    ; monoid    to +-monoid
    )

  *-promonoid : Promonoid c ℓ₁ ℓ₂
  *-promonoid = record { isPromonoid = *-isPromonoid }

  open Promonoid *-promonoid public
    using ()
    renaming
    ( magma     to *-magma
    ; semigroup to *-semigroup
    )


------------------------------------------------------------------------
-- Partially ordered structures

-- Partially ordered semigroups (posemigroups)

record IsPosemigroup {a ℓ₁ ℓ₂} {A : Set a}
                     (≈ : Rel A ℓ₁)
                     (≤ : Rel A ℓ₂)
                     (∙ : Op₂ A)
                     : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPartialOrder : IsPartialOrder ≈ ≤
    assoc          : Associative ≈ ∙
    monotonic      : ∙ Preserves₂ ≤ ⟶ ≤ ⟶ ≤

  open IsPartialOrder isPartialOrder public

  ∙-cong : Congruent₂ ≈ ∙
  ∙-cong x≈y u≈v =
    antisym (monotonic (reflexive x≈y) (reflexive u≈v))
            (monotonic (reflexive (Eq.sym x≈y)) (reflexive (Eq.sym u≈v)))

  isProsemigroup : IsProsemigroup ≈ ≤ ∙
  isProsemigroup = record
    { isSemigroup = record
      { isMagma   = record
        { isEquivalence = isEquivalence
        ; ∙-cong   = ∙-cong
        }
      ; assoc     = assoc
      }
    ; reflexive   = reflexive
    ; trans       = trans
    ; monotonic   = monotonic
    }

  open IsProsemigroup isProsemigroup public using (isSemigroup; isMagma)

record Posemigroup c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _≤_
  infixl 7 _∙_
  field
    Carrier       : Set c
    _≈_           : Rel Carrier ℓ₁  -- The underlying equality.
    _≤_           : Rel Carrier ℓ₂  -- The partial order.
    _∙_           : Op₂ Carrier     -- Multiplication.
    isPosemigroup : IsPosemigroup _≈_ _≤_ _∙_

  open IsPosemigroup isPosemigroup public

  poset : Poset c ℓ₁ ℓ₂
  poset = record { isPartialOrder = isPartialOrder }

  open Poset poset public using (preorder)

  semigroup : Semigroup c ℓ₁
  semigroup = record { isSemigroup = isSemigroup }

  open Semigroup semigroup public using (setoid; magma)

  prosemigroup : Prosemigroup c ℓ₁ ℓ₂
  prosemigroup = record { isProsemigroup = isProsemigroup }

-- Partially ordered monoids (pomonoids)

record IsPomonoid {a ℓ₁ ℓ₂} {A : Set a}
                  (≈ : Rel A ℓ₁)        -- The underlying equality.
                  (≤ : Rel A ℓ₂)        -- The partial order.
                  (∙ : Op₂ A) (ε : A)   -- The monoid.
                  : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPosemigroup : IsPosemigroup ≈ ≤ ∙
    identity      : Identity ≈ ε ∙

  open IsPosemigroup isPosemigroup public

  isPromonoid : IsPromonoid ≈ ≤ ∙ ε
  isPromonoid = record
    { isProsemigroup = isProsemigroup
    ; identity       = identity
    }

  open IsPromonoid isPromonoid public
    using (isMonoid; identityˡ; identityʳ)

record Pomonoid c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _≤_
  infixl 7 _∙_
  field
    Carrier    : Set c
    _≈_        : Rel Carrier ℓ₁  -- The underlying equality.
    _≤_        : Rel Carrier ℓ₂  -- The partial order.
    _∙_        : Op₂ Carrier     -- The monoid multiplication.
    ε          : Carrier         -- The monoid unit.
    isPomonoid : IsPomonoid _≈_ _≤_ _∙_ ε

  open IsPomonoid isPomonoid public

  posemigroup : Posemigroup c ℓ₁ ℓ₂
  posemigroup = record { isPosemigroup = isPosemigroup }

  open Posemigroup posemigroup public using
    ( setoid
    ; preorder
    ; poset
    ; magma
    ; semigroup
    ; prosemigroup
    )

  promonoid : Promonoid c ℓ₁ ℓ₂
  promonoid = record { isPromonoid = isPromonoid }

  open Promonoid promonoid public using (monoid)

-- Every bounded semilattice gives rise to a pomonoid
--
-- FIXME: this should go into
-- Relation.Binary.Properties.BoundedJoinSemilattice.

boundedJoinSemilatticeIsPomonoid
  : ∀ {a ℓ₁ ℓ₂} → BoundedJoinSemilattice a ℓ₁ ℓ₂ → Pomonoid a ℓ₁ ℓ₂
boundedJoinSemilatticeIsPomonoid boundedJoinSemilattice = record
  { Carrier = Carrier
  ; _≈_     = _≈_
  ; _≤_     = _≤_
  ; _∙_     = _∨_
  ; ε       = ⊥
  ; isPomonoid = record
    { isPosemigroup = record
      { isPartialOrder = isPartialOrder
      ; assoc          = ∨-assoc
      ; monotonic      = ∨-monotonic
      }
    ; identity         = identity
    }
  }
  where
    open BoundedJoinSemilattice boundedJoinSemilattice
    open JSProps  joinSemilattice
    open BJSProps boundedJoinSemilattice

boundedMeetSemilatticeIsPomonoid
  : ∀ {a ℓ₁ ℓ₂} → BoundedMeetSemilattice a ℓ₁ ℓ₂ → Pomonoid a ℓ₁ ℓ₂
boundedMeetSemilatticeIsPomonoid boundedMeetSemilattice = record
  { Carrier = Carrier
  ; _≈_     = _≈_
  ; _≤_     = _≤_
  ; _∙_     = _∧_
  ; ε       = ⊤
  ; isPomonoid = record
    { isPosemigroup = record
      { isPartialOrder = isPartialOrder
      ; assoc          = ∧-assoc
      ; monotonic      = ∧-monotonic
      }
    ; identity         = identity
    }
  }
  where
    open BoundedMeetSemilattice boundedMeetSemilattice
    open MSProps  meetSemilattice
    open BMSProps boundedMeetSemilattice

