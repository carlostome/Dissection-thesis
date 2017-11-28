\begin{code}
module Proposal.TotallyFree.TailRec where

  open import Data.Nat     using (ℕ ; zero; suc; _+_)
  open import Data.Sum     using (_⊎_; inj₁; inj₂)
  open import Data.Product
  open import Data.Stream
  open import Agda.Builtin.Coinduction
  open import Function
  open import Data.List hiding (length)
  open import Data.Unit
  open import Data.Empty
  open import Data.Bool
  open import Relation.Binary.PropositionalEquality
  open import Relation.Binary
  open import Relation.Binary

  open import Proposal.Expr
  open import Proposal.WellFounded.Nat
  open import Induction.WellFounded

  -- tail recursive functions [I → O]
  -- TailRec I O ~ General I (λ _ → ⊥) O
  data TailRec (I : Set) (O : Set) : Set where
    return   : O → TailRec I O
    call⟨_⟩  : I → TailRec I O

  fold : ∀ {I O} {X : Set} → (I → X) → (O → X) → TailRec I O → X
  fold f g (return x)  = g x
  fold f g call⟨ x ⟩   = f x

  -- a tail recursive program
  _⟶_ : Set → Set → Set
  I ⟶ O = (i : I) → TailRec I O

  infixr 1 _⟶_

  -- expand a TailRec given a function I → O
  expand : ∀ {I O} → I ⟶ O → TailRec I O → TailRec I O
  expand f = fold f return

  -- petrol-driven semantics
  engine : ∀ {I O} (f : I ⟶ O ) (n : ℕ) → TailRec I O → TailRec I O
  engine f zero    = id
  engine f (suc n) = engine f n ∘ expand f

  stream : ∀ {I O} (f : I ⟶ O) → TailRec I O → Stream (TailRec I O)
  stream f m = m ∷ ♯ (stream f (expand f m))

  module Example where

    foldl' : ∀ { A B : Set} → (A → B → A) → A × List B ⟶ A
    foldl' f (b , [])     = return b
    foldl' f (b , x ∷ xs) = call⟨ f b x , xs ⟩

    load/unload : (Expr ⊎ ℕ) × Stack ⟶ ℕ
    -- load
    load/unload (inj₁ (Val x) , stk)    = call⟨ inj₂ x , stk ⟩
    load/unload (inj₁ (Add l r) , stk)  = call⟨ inj₁ l , Left r stk ⟩
    -- unload
    load/unload (inj₂ v , Nil)          = return v
    load/unload (inj₂ v , Left r stk)   = call⟨ inj₁ r , Right v stk ⟩
    load/unload (inj₂ v , Right v' stk) = call⟨ inj₂ (v + v') , stk ⟩

    example : Stream (TailRec ((Expr ⊎ ℕ) × Stack) ℕ)
    example = stream load/unload call⟨ (inj₁ (Add (Val 1) (Add (Val 2) (Val 3))) , Nil) ⟩

  -- for TailRec we would like to be able to reify the BC predicate.
  -- we need a type of descriptions that capture this and then a run function
  -- over the BC that terminates.
  -- good luck!

  data CDesc (I : Set) : Set₁ where
    `1 : CDesc I
    `X : (i : I) → CDesc I

  ⟦_⟧ : ∀ { I : Set } → CDesc I → (I → Set) → Set
  ⟦ `1 ⟧ X    = ⊤
  ⟦ `X i ⟧ X  = X i

  record CFunc (I : Set) : Set₁ where
    constructor mk
    field func : I → CDesc I

  data μ {I : Set} (R : CFunc I) (i : I) : Set where
    con : ⟦ CFunc.func R i ⟧ (μ R) → μ R i

  -- from a tail recursive program prog we can build a Bove-Capretta predicate
  module BC {I : Set} {O : Set} (prog : I ⟶ O) where

    dom : TailRec I O → CDesc I
    dom (return _) = `1
    dom call⟨ a ⟩  = `X a

    Dom : CFunc I
    Dom = CFunc.mk λ x → dom (prog x)

    mutual
      run : (input : I) → μ Dom input → O
      run i (con domS)  = run1 (prog i) (mapRun {prog i} domS)
    -- --   run : (a : A) → μ Dom a → B a
    -- --   run a (con domS) = run1 (prog a) (mapRun {p = prog a} domS)

      mapRun : ∀{p : TailRec I O} → ⟦ dom p ⟧ (μ Dom) → ⟦ dom p ⟧ (λ _ → O)
      mapRun {return x₁} tt  = tt
      mapRun {call⟨ a ⟩} x   = run a x
    --   -- mapRun {p = returnRec x} tt = tt
    --   -- mapRun {p = callRec a rec} (domA , domRec) =
    --   --   run a domA , λ b → mapRun {p = rec b} (domRec b)

      run1 : (p : TailRec I O ) → ⟦ dom p ⟧ (λ _ → O) → O
      run1 (return x) tt  = x
      run1 call⟨ x ⟩ d    = d

  module Silly-Function where

    silly : ℕ ⟶ ℕ
    silly zero    = return zero
    silly (suc x) = call⟨ x ⟩

    DomSilly : ℕ → Set
    DomSilly = μ (BC.Dom silly)

    silly-bove : ∀ (n : ℕ) → DomSilly n → ℕ
    silly-bove = BC.run silly

    silly-wf : (n : ℕ) →  DomSilly n
    silly-wf zero    = con tt
    silly-wf (suc n) = con (silly-wf n)

    silly' : ℕ → ℕ
    silly' n = silly-bove n (silly-wf n)

  module TL-length where

    aux : ∀ {A : Set} → ℕ × List A ⟶ ℕ
    aux (l , [])     = return l
    aux (l , x ∷ xs) = call⟨ (1 + l) , xs ⟩

    DomAux : ∀ {A : Set} (inp : ℕ × List A) → Set
    DomAux = μ (BC.Dom aux)

    aux-bove : ∀ {A : Set} (inp : ℕ × List A) → DomAux inp → ℕ
    aux-bove = BC.run aux

    aux-wf : ∀ {A : Set} (inp : ℕ × List A) → DomAux inp
    aux-wf (l , [])     = con tt
    aux-wf (l , x ∷ xs) = con (con {!!})

  Dom-load/unload : (Expr ⊎ ℕ) × Stack → Set
  Dom-load/unload = μ (BC.Dom Example.load/unload)

  load/unload-Bove : ∀ (inp : (Expr ⊎ ℕ) × Stack) → Dom-load/unload inp → ℕ
  load/unload-Bove = BC.run Example.load/unload

  load/unload-wf : ∀ (inp : (Expr ⊎ ℕ) × Stack) → Dom-load/unload inp
  load/unload-wf = {!!}

  load-unload' : (Expr ⊎ ℕ) × Stack → ℕ
  load-unload' inp = load/unload-Bove inp (load/unload-wf inp)

  example-expr = Add (Val 1) (Add (Val 2) (Val 3))

  init : Expr → (Expr ⊎ ℕ) × Stack
  init e = inj₁ e , Nil

  -- -- Lift a WellFounded relation on I to TailRec I O for any O
  -- module WellFounded-TailRec {I O : Set} (_<_ : Rel I)
  --        (trans : Trans _<_) (wf : WF.WellFounded _<_) where
  --     -- a well founded relation implies its transitive?
  --     -- are there well founded relations that are not transitive?

  --     data _⊏_ : TailRec I O → TailRec I O → Set where
  --       ⊏-return : ∀ {i o}             → return o   ⊏ call⟨ i ⟩
  --       ⊏-call   : ∀ {i₁ i₂} → i₁ < i₂ → call⟨ i₁ ⟩ ⊏ call⟨ i₂ ⟩

  --     downwards-closed : ∀ {x y} → WF.Acc _⊏_ y → x ⊏ y → WF.Acc _⊏_ x
  --     downwards-closed (WF.acc _) ⊏-return    = WF.acc λ {_ ()}
  --     downwards-closed (WF.acc rs) (⊏-call x) = rs call⟨ _ ⟩ (⊏-call x)

  --     ⊏-return-acc : ∀ {o} → WF.Acc _⊏_ (return o)
  --     ⊏-return-acc = WF.acc λ {_ ()}

  --     accesible : ∀ {x} → WF.Acc _<_ x → WF.Acc _⊏_ call⟨ x ⟩
  --     accesible (WF.acc a) =
  --       WF.acc λ { .(return _) ⊏-return → ⊏-return-acc ;
  --                   .(call⟨ _ ⟩) (⊏-call i₁<x) →
  --                     WF.acc λ { (return _) _ → ⊏-return-acc
  --                               ; call⟨ y ⟩ (⊏-call y<i₁ ) →
  --                               accesible (a y (trans y<i₁ i₁<x))}} -- Maybe we can get ride of transitivity?

  --     accesible' : (x y : TailRec I O) → y ⊏ x → WF.Acc _⊏_ y
  --     accesible' .(call⟨ _ ⟩) .(return _) ⊏-return    = ⊏-return-acc
  --     accesible' .(call⟨ _ ⟩) .(call⟨ _ ⟩) (⊏-call x) = accesible (wf _)

  --     ⊏-WF : WF.WellFounded _⊏_
  --     ⊏-WF x = WF.acc (accesible' x)

  --     lift : (i : I) → TailRec I O
  --     lift = call⟨_⟩

  -- module Terminates {I O : Set} {_<_ : Rel I} {trans : Trans _<_} {wf : WF.WellFounded _<_} (f : I ⟶ O)  where

  --   open WellFounded-TailRec {I} {O} (_<_) trans wf

  --   data TailRecT (i : I) : I ⟶ O → Set where
  --     term   : f i ⊏ call⟨ i ⟩ → TailRecT i f

  --   -- A function f terminates iff for every input I, we
  --   -- can construct the predicate TailRecT
  --   Term : Set
  --   Term = ∀ (i : I) → TailRecT i f

  --   -- the function that actually performs recursion on the Accesibility
  --   -- predicate
  --   tail-rec-work : (i : I) → Term → WF.Acc _⊏_ (call⟨ i ⟩) → O
  --   tail-rec-work i t ac with t i
  --   tail-rec-work i t ac | term x with f i
  --   tail-rec-work i t ac | term x | return o   = o
  --   tail-rec-work i t (WF.acc ac) | term x | call⟨ y ⟩ = tail-rec-work y t (ac call⟨ y ⟩ x)

  --   -- the interface
  --   tail-rec : Term → I → O
  --   tail-rec t i = tail-rec-work i t (⊏-WF (call⟨ i ⟩))

  module Term {I O : Set} (_<_ : Rel I _) (wf : Well-founded _<_)  where

    Step : I → TailRec I O → Set
    Step _ (return x) = ⊤
    Step i call⟨ i′ ⟩ = i′ < i

    Terminates : (I ⟶ O) → Set
    Terminates f = (i : I) → Step i (f i)

    tail-rec-work : (inp : I) (f : I ⟶ O) → Terminates f → Acc _<_ inp → O
    tail-rec-work inp f term wf with term inp
    ... | Ti with f inp
    tail-rec-work inp f term wf | tt | return x = x
    tail-rec-work inp f term (acc ac) | x<i | call⟨ x ⟩ = tail-rec-work x f term (ac x x<i)

    tail-rec : (inp : I) → (f : I ⟶ O) → Terminates f → O
    tail-rec i f term = tail-rec-work i f term (wf i)

  -- An example of how I'd like to use the above machinery
  -- module Examples where
  --   open import Proposal.WellFounded.Nat

  --   length : ∀ {A : Set} → List A → ℕ
  --   length []       = 0
  --   length (_ ∷ xs) = 1 + length xs

  --   module Length {A : Set} where

  --     open Version-2
  --     open Inverse-image (_<ℕ_) length 

  --     open Inverse-image {ℕ × List A} (_⊰L_) proj₂ public

  --     ⊰-wf : WF.WellFounded _⊰_
  --     ⊰-wf = ii-wf (ii-wfL <ℕ-WF)

  --     aux : ∀ {A : Set} → ℕ × List A ⟶ ℕ
  --     aux (l , [])     = return l
  --     aux (l , x ∷ xs) = call⟨ (1 + l) , xs ⟩

  --     aux-term : Term.Terminates _⊰_ ⊰-wf aux
  --     aux-term (n , [])     = tt
  --     aux-term (n , x ∷ xs) = Base

  --     len : ℕ × List A → ℕ
  --     len i = Term.tail-rec _⊰_ ⊰-wf i aux aux-term

  --   module Foldl {A B : Set} where

  --     open Inverse-image-Well-founded {List B} (_<ℕ_) length public renaming (_⊰_ to _⊰L_; ii-wf to ii-wfL)

  --     open Inverse-image-Well-founded {(A → B → A) × A × List B} (_⊰L_) (proj₂ ∘ proj₂) public

  --     ⊰-wf : WF.WellFounded _⊰_
  --     ⊰-wf = ii-wf (ii-wfL <ℕ-WF)

  --     foldl-aux : (A -> B -> A) × A × List B ⟶ A
  --     foldl-aux (f , b , [])       = return b
  --     foldl-aux (f , b , (x ∷ xs)) = call⟨ f , f b x , xs ⟩

  --     foldl-term : Term.Terminates _⊰_ ⊰-wf foldl-aux
  --     foldl-term (f , b , [])     = tt
  --     foldl-term (f , b , x ∷ xs) = Base

  --     foldl' : (A -> B -> A) × A × List B → A
  --     foldl' i = Term.tail-rec _⊰_ ⊰-wf i foldl-aux foldl-term

  --   module Reverse {A : Set} where

  --     open Inverse-image-Well-founded {List A} (_<ℕ_) length public renaming (_⊰_ to _⊰L_; ii-wf to ii-wfL)

  --     open Inverse-image-Well-founded {List A × List A} (_⊰L_) proj₂ public

  --     ⊰-wf : WF.WellFounded _⊰_
  --     ⊰-wf = ii-wf (ii-wfL <ℕ-WF)

  --     rev-aux : List A × List A ⟶ List A
  --     rev-aux (a , [])   = return a
  --     rev-aux (a , x ∷ xs) = call⟨ (x ∷ a) , xs ⟩

  --     rev-term : Term.Terminates _⊰_ ⊰-wf rev-aux
  --     rev-term (_ ,  [])     = tt
  --     rev-term (_ ,  x ∷ xs) = Base

  --     rev' : List A × List A → List A
  --     rev' i = Term.tail-rec _⊰_ ⊰-wf i rev-aux rev-term

  --     rev : List A → List A
  --     rev xs = rev' ([] , xs)

  --   module Even where

  --     mutual
  --       even : ℕ → Bool
  --       even zero    = true
  --       even (suc n) = odd n

  --       odd : ℕ → Bool
  --       odd zero    = false
  --       odd (suc n) = even n

  --     even/odd-aux : (ℕ ⊎ ℕ) ⟶ Bool
  --     even/odd-aux (inj₁ zero)    = return true
  --     even/odd-aux (inj₁ (suc x)) = call⟨ inj₂ x ⟩
  --     even/odd-aux (inj₂ zero)    = return false
  --     even/odd-aux (inj₂ (suc y)) = call⟨ inj₁ y ⟩

  --     open Inverse-image-Well-founded {ℕ ⊎ ℕ} (_<ℕ_) (λ {(inj₁ x) → x ; (inj₂ y) → y})

  --     even/odd-term : Term.Terminates _⊰_ (ii-wf <ℕ-WF) even/odd-aux
  --     even/odd-term (inj₁ zero)    = tt
  --     even/odd-term (inj₁ (suc x)) = Base
  --     even/odd-term (inj₂ zero)    = tt
  --     even/odd-term (inj₂ (suc y)) = Base

  --     even' : ℕ → Bool
  --     even' i = Term.tail-rec _⊰_ (ii-wf <ℕ-WF) (inj₁ i) even/odd-aux even/odd-term

  --     odd' : ℕ → Bool
  --     odd' i = Term.tail-rec _⊰_ (ii-wf <ℕ-WF) (inj₂ i) even/odd-aux even/odd-term
\end{code}
