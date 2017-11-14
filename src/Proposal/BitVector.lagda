\begin{code}
module Proposal.BitVector where

  open import Data.Sum
  open import Data.Nat
  open import Data.Nat.Properties as Nat
  open import Relation.Binary.PropositionalEquality
  open import Proposal.WellFounded.Nat
  open import Proposal.WellFounded.WellFounded
  open import Data.Empty
  open import Data.Maybe
  open import Data.Product

  data Bit : Set where
    #1 : Bit
    #0 : Bit

  not : Bit → Bit
  not #1 = #0
  not #0 = #1

  data _<Bit_ : Bit → Bit → Set where
    #0<#1 : #0 <Bit #1

  <Bit-WF : WF.WellFounded _<Bit_
  <Bit-WF x = WF.acc (aux x)
    where
      aux : (x y : Bit) → y <Bit x → WF.Acc _<Bit_ y
      aux .#1 .#0 #0<#1 = WF.acc λ {_ ()}

  module Bound where
    data BitVector : ℕ → Set where
      _▸  : Bit   → BitVector 1
      _፥_ : ∀ {n} → Bit → BitVector n → BitVector (1 + n)

    infixl 40 _▸
    infixr 30 _፥_

    data [_]_<BV_ : (n : ℕ) → BitVector n → BitVector n → Set where
      BV-Base : ∀     {x y}              → x <Bit y            → [ 1 ]          x ▸ <BV y ▸
      BV-Stop : ∀ {n} {x y} {bin₁ bin₂}  → x <Bit y            → [ 1 + n ] x ፥ bin₁ <BV y ፥ bin₂
      BV-Step : ∀ {n} {x}   {bin₁ bin₂}  → [ n ] bin₁ <BV bin₂ → [ 1 + n ] x ፥ bin₁ <BV x ፥ bin₂

    -- mutual
    --   acc2 : ∀ {n} (b : Bin n) → WF.Acc [ n ]_<Bin_ b

    --   acc2 .bin₂ x₁ .(BMore 0′ bin₁) (BStop {n} {.0′} {.1′} {bin₁} {bin₂} 0<1) = WF.acc (acc3 bin₁ (<Bin-wf n bin₁))
    --   acc2 _ (WF.acc x₁) .(BMore 1′ _) (BStep x₂) = WF.acc (acc2 _ (x₁ _ x₂))

    --   acc3 : ∀ {n} (b : Bin n) → WF.Acc [ n ]_<Bin_ b
    --                           → (∀ y → [ suc n ] y <Bin (BMore 0′ b) → WF.Acc [ suc n ]_<Bin_ y)
    --   acc3 b x .(BMore _ _) (BStop ())
    --   acc3 b (WF.acc x) .(BMore 0′ _) (BStep x₁) = WF.acc (acc3 _ (x _ x₁))

    --   <Bin-wf : ∀ n → WF.WellFounded [ n ]_<Bin_
    --   <Bin-wf n x = WF.acc (aux n x)
    --     where
    --       aux : (n : ℕ) (x y : Bin n) → [ n ] y <Bin x → WF.Acc ([_]_<Bin_ n) y
    --       aux .1 .(BOne 1′) .(BOne 0′) (BBase {.0′} {.1′} 0<1) = WF.acc λ { .(BOne _) (BBase ())}
    --       aux .(suc n) .(BMore 1′ bin₂) .(BMore 0′ bin₁) (BStop {n} {.0′} {.1′} {bin₁} {bin₂} 0<1) = WF.acc (acc3 bin₁ (<Bin-wf n bin₁))
    --       aux .(suc n) .(BMore 1′ bin₂) .(BMore 1′ bin₁) (BStep {n} {1′} {bin₁} {bin₂} p) = WF.acc (acc2 bin₁ (<Bin-wf n bin₁))
    --       aux .(suc n) .(BMore 0′ bin₂) .(BMore 0′ bin₁) (BStep {n} {0′} {bin₁} {bin₂} p) = WF.acc (acc3 bin₁ (aux n bin₂ bin₁ p))

    _++BV_ : ∀ {n m} → BitVector n → BitVector m → BitVector (n + m)
    (x ▸) ++BV y    = x ፥ y
    (x ፥ xs) ++BV y = x ፥ (xs ++BV y)

    appBV : ∀ {n} → Bit → BitVector n → BitVector (1 + n)
    appBV b (x ▸)    = x ፥ b ▸
    appBV b (x ፥ bv) = x ፥ (appBV b bv)

    revBV : ∀ {n} → BitVector n → BitVector n
    revBV (x ▸)    = x ▸
    revBV (x ፥ xs) = appBV x (revBV xs)

    pad : ∀ {n} → Bit → BitVector (1 + n)
    pad {zero} b  = b ▸
    pad {suc n} b = b ፥ pad b

    BigE : ℕ → Set
    BigE = BitVector

    LittleE : ℕ → Set
    LittleE = BitVector

    decr : ∀ {n} → LittleE n → Maybe (LittleE n)
    decr (#1 ▸) = just (#0 ▸)
    decr (#0 ▸) = nothing
    decr (#1 ፥ xs) = just (#0 ፥ xs)
    decr (#0 ፥ xs) with decr xs
    decr (#0 ፥ xs) | just x  = just (#1 ፥ x)
    decr (#0 ፥ xs) | nothing = nothing

    from : ∀ {n} → BigE n → LittleE n
    from = revBV

    to : ∀ {n} → LittleE n → BigE n
    to = revBV

    decr' : ∀ {n} → BigE n → Maybe (BigE n)
    decr' x with decr (from x)
    decr' x | just xs = just (to xs)
    decr' x | nothing = nothing

    theorem : ∀ {n} (bs : BigE n) → Σ (BigE n) λ xs → decr' bs ≡ just xs → [ n ] xs <BV bs 
    theorem (#1 ▸)   = (#0 ▸) , λ { refl → BV-Base #0<#1}
    theorem (#0 ▸)   =  #0 ▸  , λ {()}
    theorem (x ፥ #1 ▸) = {!!} , {!!}
    theorem (x ፥ #0 ▸) = {!!}
    theorem (x ፥ y ፥ bs) = {!!} , {!!}

    -- -- little endian representation of BitVectors
    -- data VectorBit : ℕ → Set where
    --   ◂_  :  ∀ {n} → Bit → VectorBit (1 + n)
    --   _፥_  : ∀ {n} → VectorBit n → Bit → VectorBit (1 + n)

    -- infixl 40 ◂_

    -- decr : ∀ {n} → VectorBit n → Maybe (VectorBit n)
    -- decr (◂ #1) = just (◂ #0)
    -- decr (◂ #0) = nothing
    -- decr (bs ፥ #1) = just (bs ፥ #0)
    -- decr (bs ፥ #0) with decr bs
    -- decr (bs ፥ #0) | just xs = just (xs ፥ #1)
    -- decr (bs ፥ #0) | nothing = nothing

    -- incr : ∀ {n} → VectorBit n → Maybe (VectorBit n)
    -- incr (◂ #1) = nothing
    -- incr (◂ #0) = just (◂ #1)
    -- incr (bs ፥ #0) = just (bs ፥ #1)
    -- incr (bs ፥ #1) with incr bs
    -- incr (bs ፥ #1) | just xs = just (xs ፥ #0)
    -- incr (bs ፥ #1) | nothing = nothing

    -- -- properties
    -- incr∘decr : ∀ {n} (xs : VectorBit n)
    --           → Σ (VectorBit n) λ ys → incr xs ≡ just ys → decr ys ≡ just xs
    -- incr∘decr = {!!}

    -- decr∘incr : ∀ {n} (xs : VectorBit n)
    --           → Σ (VectorBit n) λ ys → decr xs ≡ just ys → incr ys ≡ just xs
    -- decr∘incr = {!!}

    -- from : ∀ {n} → VectorBit n → BitVector n
    -- from {zero} ()
    -- from {suc zero} (◂ x)      = x ▸
    -- from {suc (suc n)} (◂ x)   = appBV x (pad #0)
    -- from {suc zero} (() ፥ _)
    -- from {suc (suc n)} (bs ፥ b) = appBV b (from bs)

    -- to : ∀ {n} → BitVector n → VectorBit n 
    -- to {zero} ()
    -- to {suc zero} (x ▸) = ◂ x
    -- to {suc zero} (x ፥ ())
    -- to {suc (suc n)} (b ፥ bs) = {!!}

    -- incr' : ∀ {n} → BitVector n → Maybe (BitVector n)
    -- incr' bs with incr (to bs)
    -- incr' bs | just x  = just (from x)
    -- incr' bs | nothing = nothing

    -- -- properties
    -- to∘from : ∀ {n} → (bs : VectorBit n) → to (from bs) ≡ bs
    -- to∘from bs = {!!}

    -- from∘to : ∀ {n} → (bs : BitVector n) → from (to bs) ≡ bs
    -- from∘to = {!!}


  module UnBound where

    data BitVector : Set where
      _▸   : Bit → BitVector
      _፥_ : Bit → BitVector → BitVector

    infixl 40 _▸
    infixr 30 _፥_

    data _<BV_ : BitVector → BitVector → Set where
      BV-Base : ∀ {x y}              → x <Bit y            → x ▸ <BV y ▸
      BV-Stop : ∀ {x y} {bin₁ bin₂}  → x <Bit y            → x ፥ bin₁ <BV y ፥ bin₂
      BV-Step : ∀ {x}   {bin₁ bin₂}  → bin₁ <BV bin₂       → x ፥ bin₁ <BV x ፥ bin₂
      BV-Succ-L : ∀ {x}   {bin₂}     → #0 ▸ <BV bin₂       → x ▸ <BV x ፥ bin₂
      BV-Succ-R : ∀ {x}   {bin₁}     → bin₁ <BV #0 ▸       → x ፥ bin₁ <BV x ▸

    p : (#1 ፥ (#0 ▸)) <BV (#1 ▸)
    p = {!!}
    mutual
    --   acc2 : ∀ {n} (b : Bin n) → WF.Acc [ n ]_<Bin_ b

    --   acc2 .bin₂ x₁ .(BMore 0′ bin₁) (BStop {n} {.0′} {.1′} {bin₁} {bin₂} 0<1) = WF.acc (acc3 bin₁ (<Bin-wf n bin₁))
    --   acc2 _ (WF.acc x₁) .(BMore 1′ _) (BStep x₂) = WF.acc (acc2 _ (x₁ _ x₂))

      acc3 : ∀ (b : BitVector) → (∀ y → y <BV (#0 ፥ b) → WF.Acc _<BV_ y)
      acc3 b .(_ ፥ _) (BV-Stop ())
      acc3 b .(#0 ፥ _) (BV-Step x₁) = WF.acc (acc3 {!!})
      acc3 b .(#0 ▸) (BV-Succ-L x₁) = {!!}

      acc : ∀ y → y <BV #0 ▸ → WF.Acc _<BV_ y
      acc .(_ ▸) (BV-Base ())
      acc .(#0 ፥ _) (BV-Succ-R x) = WF.acc (acc3 _)
    --   acc3 b x .(BMore _ _) (BStop ())
    --   acc3 b (WF.acc x) .(BMore 0′ _) (BStep x₁) = WF.acc (acc3 _ (x _ x₁))

      <Bin-WF : WF.WellFounded _<BV_
      <Bin-WF x = WF.acc (aux x)
        where
          aux : (x y : BitVector) →  y <BV x → WF.Acc (_<BV_) y
          aux (.#1 ▸) .(#0 ▸) (BV-Base #0<#1) = WF.acc λ {y x₁ → {!x₁!}}
          aux (x ▸) .(x ፥ bin₁) (BV-Succ-R {bin₁ = bin₁} p) = {!!}
          aux (.#1 ፥ x) .(#0 ፥ _) (BV-Stop #0<#1) = {!!}
          aux (x₁ ፥ x) .(x₁ ፥ _) (BV-Step p) = {!!}
          aux (b ፥ .(_ ▸)) .(b ▸) (BV-Succ-L (BV-Base x₁)) = {!!}
          aux (b ፥ .(#0 ፥ _)) .(b ▸) (BV-Succ-L (BV-Succ-L p₁)) = {!!}

    module Stack where
