\begin{code}
module Proposal.Sized.Nat where

  open import Data.Bool          using (true; false; Bool)
  open import Agda.Builtin.Size

  data SNat : {_ : Size} → Set where
    Szero : {i : Size} → SNat {↑ i}
    Ssuc  : {i : Size} → SNat {i}   → SNat {↑ i}

  _≤_ : ∀ {i j : Size} → SNat {i} → SNat {j} → Bool
  Szero ≤ y        = true
  Ssuc x ≤ Szero   = false
  Ssuc x ≤ Ssuc y  = x ≤ y

  monus : ∀ {i : Size} → SNat {i} → SNat {ω} → SNat {i}
  monus Szero y           = Szero
  monus (Ssuc x) Szero    = Ssuc x
  monus (Ssuc x) (Ssuc y) = monus x y

  div : ∀ {i : Size} → SNat {i} → SNat {ω} → SNat {i}
  div Szero y     = Szero                    -- 0 `div` x = 0
  div (Ssuc x) y  = Ssuc (div (monus x y) y) -- (1 + n) `div` y = 1 + ((n - y) `div` y)

  -- we really need to pass around sizes
  gcd : ∀ {i j : Size} → SNat {i} → SNat {j} → SNat {i ⊔ˢ j}
  gcd {.(↑ _)} {j} Szero y             = y                 -- gcd(0,y) = y
  gcd {.(↑ _)} {.(↑ _)} (Ssuc x) Szero = Ssuc x            -- gcd(x,0) = x
  gcd {.(↑ i)} {.(↑ j)} (Ssuc {i} x) (Ssuc {j} y) with x ≤ y
  ... | true  = gcd {↑ i} {j} (Ssuc x) (monus {j} y x)     -- gcd(1+x , 1+y) = gdc (Ssuc x , y `monus` x)
  ... | false = gcd {i} {↑ j} (monus {i} x y) (Ssuc y)     -- gcd(1+x , 1+y) = gdc (x `monus` y, Ssuc y)
\end{code}
