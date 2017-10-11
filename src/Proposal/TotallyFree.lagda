\begin{code}
module Proposal.TotallyFree where

  open import Data.Nat
  open import Data.Bool
  open import Data.List
  open import Function

  module Monad where

    data General (S : Set) (T : S → Set) (X : Set) : Set where
      !!   : X → General S T X
      _??_ : (s : S) → (T s → General S T X) → General S T X

    infixr 5 _??_

    fold : ∀ {l} {S T X } {Y : Set l} → (X → Y) → ((s : S) → (T s → Y) → Y) → General S T X → Y
    fold b r (!! x)   = b x
    fold b r (s ?? x) = r s (λ z → fold b r (x z))

    _>>=_ : ∀ {S T X Y} → General S T X → (X → General S T Y) → General S T Y
    m >>= f = fold f _??_ m

    infixr 4 _>>=_

    call : ∀ {S T} → (s : S) → General S T (T s)
    call s = s ?? !!

    PiG : (S : Set) (T : S → Set) → Set
    PiG S T = (s : S ) → General S T (T s)

    example : PiG ℕ λ _ → ℕ
    example zero    = !! zero
    example (suc n) = call n >>= λ fn → call fn >>= λ ffn → !! (suc ffn)

    module QuickSort where

      -- something is going on with Applicative vs Monad
      -- for nested recursion it is clear that we need the full monadic interface, however to
      -- simple recursion we do not
      quickSort : ∀ {A : Set} → (A → A → Bool) → PiG (List A) λ _ → (List A)
      quickSort leq []       = !! []
      quickSort leq (x ∷ xs) =
          call (filter (leq x) xs)         >>= λ smaller
        → call (filter (not ∘ (leq x)) xs) >>= λ bigger
        → !! (smaller ++ [ x ] ++ bigger)

--   module Applicative where

--     -- simple recursion, not tail recursion
--     data Rec (I : Set) (O : Set) (X : Set) : Set where
--       !!    : X → Rec I O X
--       _<*>_ : {!General F (X → Y)!} -> {!!} -> {!!}

-- -- data FreeAL f a
-- -- = PureL a
-- -- | ∀b.FreeAL f (b → a) :*: f b

--     _<$>_ : {!!}
--     _<$>_ = {!!}

--     infixl 4 _<*>_
--     infixl 5 _<$>_

--     rec-call : ∀ {I O X} →  X → Rec I O X
--     rec-call s = {!!}

--     _⟶_ : (S : Set) → (T : Set) → Set
--     S ⟶ T = (s : S) → Rec S T T

--     infixr 4 _⟶_
--     -- pig : (S : Set) → (T : Set) → Set
--     -- PiG S T = (s : S ) → {!!} -- General S T (T s)

--     quickSort : ∀ {A : Set} → (A → A → Bool) → List A ⟶ List A
--     quickSort leq []       = !! []
--     quickSort leq (x ∷ xs) = rec-call (filter (leq x) xs) <*> rec-call (filter (not ∘ (leq x)) xs)
--                                                       <$> (λ smaller bigger → smaller ++ [ x ] ++ bigger)

--     len : ∀ { A : Set} → (List A) ⟶ ℕ
--     len []       = !! zero
--     len (x ∷ xs) = rec-call xs <$> (λ n → n + 1)

--     fold : ∀ {A B : Set} → (A → B → B) → B → List A ⟶ B
--     fold f b []       = !! b
--     fold f b (x ∷ xs) = rec-call xs <*> (λ r → f x r)

--     ma : ∀ {A B : Set} → (A → B ) → List A ⟶ List B
--     ma f []       = !! []
--     ma f (x ∷ xs) = rec-call xs <*> (λ ys → f x ∷ ys)


    -- tail call recursion looks like the either monad
  data TailRec (I : Set) (O : Set) : Set where
    return     : O → TailRec I O
    tail-call  : I → TailRec I O

  fold-TailRec : ∀ {X I} {Y : Set} → (X → Y) → (I → Y) → TailRec I X → Y
  fold-TailRec f g (return x)    = f x
  fold-TailRec f g (tail-call x) = g x

  open import Data.Nat     using (ℕ ; zero; suc; _+_)
  open import Data.Sum     using (_⊎_; inj₁; inj₂)
  open import Data.Product
  open import Data.Stream

  open import Agda.Builtin.Coinduction
  open import Proposal.WellFounded.WellFounded

  data Expr : Set where
    Val : ℕ -> Expr
    Add : Expr -> Expr -> Expr

  size : Expr → ℕ
  size (Val x) = 1
  size (Add l r) = size l + size r + 1

  eval : Expr -> ℕ
  eval (Val x) = x
  eval (Add l r) = eval l + eval r

  data Stack : Set where
    Nil   : Stack
    Left  : Expr -> Stack -> Stack
    Right : ℕ -> Stack -> Stack

  _⟶ₜ_ : Set → Set → Set
  I ⟶ₜ O = (i : I) → TailRec I O

  load/unload : ((Expr ⊎ ℕ) × Stack) ⟶ₜ ℕ
  -- load
  load/unload (inj₁ (Val x) , stk)    = tail-call (inj₂ x , stk)
  load/unload (inj₁ (Add l r) , stk)  = tail-call (inj₁ l , Left r stk)
  -- unload
  load/unload (inj₂ v , Nil)          = return v
  load/unload (inj₂ v , Left r stk)   = tail-call (inj₁ r , Right v stk)
  load/unload (inj₂ v , Right v' stk) = tail-call (inj₂ (v + v') , stk)

  expand : ∀ {I O} → I ⟶ₜ O → TailRec I O → TailRec I O
  expand f (return x)    = return x
  expand f (tail-call x) = f x

  example-expr = Add (Val 1) (Add (Val 2) (Val 3))

  init : Expr → (Expr ⊎ ℕ) × Stack
  init e = inj₁ e , Nil

  engine : ∀ {I O} (f : I ⟶ₜ O ) (n : ℕ) → TailRec I O → TailRec I O
  engine f zero    = id
  engine f (suc n) = engine f n ∘ expand f

  run : ∀ {I O} (f : I ⟶ₜ O) → TailRec I O → Stream (TailRec I O)
  run f m = m ∷ ♯ (run f (expand f m))

  foldl' : ∀ { A B : Set} → (A → B → A) → (A × List B) ⟶ₜ A
  foldl' f (b , [])     = return b
  foldl' f (b , x ∷ xs) = tail-call (f b x , xs)

--   -- is input a parameter, an index?
--   data TailRecWF (I : Set) (input : I) (_<_ : I → I → Set) (O : Set) : Set where
--     return-wf     :  O                      → TailRecWF I input _<_ O
--     tail-call-wf  : (rec : I) → rec < input → TailRecWF I input _<_ O

--   _⟶[_]_ : (I : Set) → (I → I → Set) → Set → Set
--   I ⟶[ R ] O = (i : I) → TailRecWF I i R O

--   expand-wf : ∀ {I O _<_} {i rec : I}
--             → I ⟶[ _<_ ] O
--             → TailRecWF I i _<_ O → TailRecWF I rec _<_ O
--   expand-wf f (return-wf x)        = return-wf x
--   expand-wf f (tail-call-wf rec x) = f {!!}


--   compute : ∀ {I O : Set} {_<_ : Rel I} {input : I}
--           → I ⟶[ _<_ ] O → TailRecWF I input _<_ O → WF.Well-founded _<_ → O
--   compute f t wf = {!!}

--   data _<ℕ_ (n : ℕ) : (m : ℕ) → Set where
--     Base : n <ℕ suc n
--     Step : ∀ {m : ℕ} → n <ℕ m → n <ℕ suc m

--   loop : ℕ ⟶[ _<ℕ_ ] ℕ
--   loop zero          = return-wf zero
--   loop (suc zero)    = return-wf zero
--   loop (suc (suc n)) = tail-call-wf (suc n) Base

--   bad-loop : ℕ ⟶[ _<ℕ_ ] ℕ
--   bad-loop n = tail-call-wf n {!!}

-- -- is input a parameter, an index?
--   data TailRecWF2 (I : Set) (O : Set) : I → Set where
--     return-wf-2     : ∀ {rec : I} → O         → TailRecWF2 I O rec
--     tail-call-wf-2  : ∀             (rec : I) → TailRecWF2 I O rec

--   -- expand-wf-2 : ∀ {I O} {rec₁ rec₂ : I}
--   --             → 
--   _⟶[_]2_ : (I : Set) → (I → I → Set) → Set → Set
--   I ⟶[ R ]2 O = (i : I) → (∀ {rec : I} → TailRecWF2 I O i × R rec i)

--   loop2 : ℕ ⟶[ _<ℕ_ ]2 ℕ
--   loop2 zero          = return-wf-2 zero , {!!}
--   loop2 (suc n)       = (tail-call-wf-2 (suc n)) , {!!}

  
\end{code}
