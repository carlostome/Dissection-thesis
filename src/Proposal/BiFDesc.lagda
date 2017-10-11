{-# OPTIONS --allow-unsolved-metas #-}
\begin{code}
module Proposal.BiFDesc where

  open import Data.Sum     using (_⊎_; inj₁; inj₂)
  open import Data.Product using (_×_; _,_)
  open import Data.Unit    using (⊤; tt)
  open import Data.Empty   using (⊥)
  open import Data.Nat     using (ℕ; suc; zero)

  open import Proposal.FDesc
\end{code}

\begin{code}
  data BiFDesc : Set₁ where
    K₂   : (A : Set)       -> BiFDesc
    1′   :                    BiFDesc
    2′   :                    BiFDesc
    _+₂_ : (P Q : BiFDesc) -> BiFDesc
    _×₂_ : (P Q : BiFDesc) -> BiFDesc
    C    : FDesc           -> BiFDesc
    J    : FDesc           -> BiFDesc

  infixl 30 _+₂_
  infixl 40 _×₂_

  ⟦_⟧₂  : BiFDesc -> Set -> Set -> Set
  ⟦ 1′     ⟧₂  X Y = X
  ⟦ 2′     ⟧₂  X Y = Y
  ⟦ K₂ A   ⟧₂  X Y = A
  ⟦ P +₂ Q ⟧₂  X Y = (⟦ P ⟧₂ X Y) ⊎ (⟦ Q ⟧₂ X Y)
  ⟦ P ×₂ Q ⟧₂  X Y = (⟦ P ⟧₂ X Y) × (⟦ Q ⟧₂ X Y)
  ⟦ C P    ⟧₂  X Y = ⟦ P ⟧₁ X
  ⟦ J Q    ⟧₂  X Y = ⟦ Q ⟧₁ Y

  module Either-Example where

    data Either (A B : Set) : Set where
      Left  : A -> Either A B
      Right : B -> Either A B

    Either-BiFDesc : BiFDesc
    Either-BiFDesc  = 1′ +₂ 2′

    Either′ : Set -> Set -> Set
    Either′ = ⟦ Either-BiFDesc ⟧₂

    pattern Left′ x = inj₁ x
    pattern Right′ x = inj₂ x

    from :  ∀ {A B : Set} -> Either A B -> Either′ A  B
    from (Left x)  = Left′ x
    from (Right x) = Right′ x

    to : ∀ {A B : Set} -> Either′ A  B -> Either A B
    to (Left′ x)  = Left x
    to (Right′ y) = Right y

  bimap : ∀ {A B C D : Set} (BF : BiFDesc) -> (A -> C) -> (B -> D) -> ⟦ BF ⟧₂ A B -> ⟦ BF ⟧₂ C D
  bimap (K₂ A)   f g x        = x
  bimap 1′       f g x        = f x
  bimap 2′       f g x        = g x
  bimap (P +₂ Q) f g (inj₁ x) = inj₁ (bimap P f g x)
  bimap (P +₂ Q) f g (inj₂ y) = inj₂ (bimap Q f g y)
  bimap (P ×₂ Q) f g (x , y)  = bimap P f g x , bimap Q f g y
  bimap (C F)    f g x        = fmap F f x
  bimap (J G)    f g x        = fmap G g x

  module Origami where

    data μ₂ ( F : BiFDesc) (A : Set) : Set where
      μ₂-in : ⟦ F ⟧₂ (μ₂ F A) A -> μ₂ F A

    module BTree-Example where

      data BTree ( A : Set) : Set where
        Leaf : A -> BTree A
        Node : BTree A -> BTree A -> BTree A

      BTree-BiFDesc : BiFDesc
      BTree-BiFDesc = 2′ +₂ 1′ ×₂ 1′

      BTree′ : Set -> Set
      BTree′ = μ₂ BTree-BiFDesc

      pattern Leaf′ x     = μ₂-in (inj₁ x)
      pattern Node′ t₁ t₂ = μ₂-in (inj₂ ( t₁ , t₂ ))

      from : ∀ {A : Set} -> BTree A -> BTree′ A
      from (Leaf x)     = Leaf′ x
      from (Node t₁ t₂) = Node′ (from t₁) (from t₂)

      to : ∀ {A : Set} -> BTree′ A -> BTree A
      to (Leaf′ x)     = Leaf x
      to (Node′ t₁ t₂) = Node (to t₁) (to t₂)
\end{code}
