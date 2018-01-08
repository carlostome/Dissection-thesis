\begin{code}
module Proposal.Derive where

  open import Data.Sum     using (_⊎_; inj₁; inj₂)
  open import Data.Product
  open import Data.Unit    using (⊤; tt)
  open import Data.Empty   using (⊥)
  open import Relation.Binary.PropositionalEquality
  open import Data.Maybe
  open import Function
  open import Data.List
  open import Data.Nat
  open import Data.List.Properties
  open import Data.List.Reverse
  open import Data.Bool
  open import Induction.WellFounded

  data U : Set where
    0′    : U
    1′    : U
    I     : U
    _⨁_  : (P Q : U)  → U
    _⨂_  : (P Q : U)  → U

  infixl 30 _⨁_
  infixl 40 _⨂_

  ⟦_⟧ : U → (Set → Set)
  ⟦ 0′ ⟧ X  = ⊥
  ⟦ 1′ ⟧ X  = ⊤
  ⟦ I ⟧  X  = X
  ⟦ F ⨁ G ⟧ X = ⟦ F ⟧ X ⊎ ⟦ G ⟧ X
  ⟦ F ⨂ G ⟧ X = ⟦ F ⟧ X × ⟦ G ⟧ X

  data μ (u : U) : Set where
    In : ⟦ u ⟧ (μ u) → μ u

  ϑ : U → U
  ϑ 0′  = 0′
  ϑ 1′  = 0′
  ϑ I   = 1′
  ϑ (f ⨁ g) = ϑ f ⨁ ϑ g
  ϑ (f ⨂ g) = ϑ f ⨂ g ⨁ f ⨂ ϑ g

  first : ∀ {X : Set} → (u : U) → ⟦ u ⟧ X → Maybe (⟦ ϑ u ⟧ X × X)
  first 0′ ()
  first 1′ x = nothing
  first I x  = just (tt , x)
  first (u ⨁ v) (inj₁ x) with first u x
  first (u ⨁ v) (inj₁ x) | just (du , x′) = just (inj₁ du , x′)
  first (u ⨁ v) (inj₁ x) | nothing        = nothing
  first (u ⨁ v) (inj₂ y) with first v y
  first (u ⨁ v) (inj₂ y) | just (x′ , dv) = just (inj₂ x′ , dv)
  first (u ⨁ v) (inj₂ y) | nothing        = nothing
  first (u ⨂ v) (u′ , v′) with first u u′
  first (u ⨂ v) (u′ , v′) | just (du , x) = just (inj₁ (du , v′) , x)
  first (u ⨂ v) (u′ , v′) | nothing with first v v′
  first (u ⨂ v) (u′ , v′) | nothing | just (dv , x) = just ((inj₂ (u′ , dv)) , x)
  first (u ⨂ v) (u′ , v′) | nothing | nothing       = nothing

  right : ∀ {X : Set} → (u : U) → ⟦ ϑ u ⟧ X × X → (⟦ ϑ u ⟧ X × X) ⊎ (⟦ u ⟧ X)
  right 0′ (() , _)
  right 1′ (() , _)
  right I (tt , x) = inj₂ x
  right (u ⨁ v) (inj₁ du , x) with right u (du , x)
  right (u ⨁ v) (inj₁ du , x) | inj₁ (du′ , x′) = inj₁ ((inj₁ du′) , x′)
  right (u ⨁ v) (inj₁ du , x) | inj₂ u′         = inj₂ (inj₁ u′)
  right (u ⨁ v) (inj₂ dv , x) with right v (dv , x)
  right (u ⨁ v) (inj₂ dv , x) | inj₁ (dv′ , x′) = inj₁ ((inj₂ dv′) , x′)
  right (u ⨁ v) (inj₂ dv , x) | inj₂ v′         = inj₂ (inj₂ v′)
  right (u ⨂ v) (inj₁ (du , v′) , x) with right u (du , x)
  right (u ⨂ v) (inj₁ (du , v′) , x) | inj₁ (du′ , x′) = inj₁ ((inj₁ (du′ , v′)) , x′)
  right (u ⨂ v) (inj₁ (du , v′) , x) | inj₂ u′ with first v v′
  right (u ⨂ v) (inj₁ (du , v′) , x) | inj₂ u′ | just (dv , x′′) = inj₁ (inj₂ (u′ , dv) , x′′)
  right (u ⨂ v) (inj₁ (du , v′) , x) | inj₂ u′ | nothing         = inj₂ (u′ , v′)
  right (u ⨂ v) (inj₂ (u′ , dv) , x) with right v (dv , x)
  right (u ⨂ v) (inj₂ (u′ , dv) , x) | inj₁ (dv′ , x′) = inj₁ (inj₂ (u′ , dv′) , x′)
  right (u ⨂ v) (inj₂ (u′ , dv) , x) | inj₂ v′         = inj₂ (u′ , v′)


  lt : {X : Set} (u : U) → ⟦ ϑ u ⟧ X → ⟦ ϑ u ⟧ X → Set
  lt 0′ () x₁
  lt 1′ () x₁
  lt I tt tt        = ⊥
  lt (u ⨁ v) (inj₁ x) (inj₁ y) = lt u x y
  lt (u ⨁ v) (inj₁ x) (inj₂ y) = ⊥
  lt (u ⨁ v) (inj₂ y) (inj₁ x) = ⊥
  lt (u ⨁ v) (inj₂ y) (inj₂ x) = lt v y x
  lt (u ⨂ v) (inj₁ (du , _)) (inj₁ (du′ , _)) = lt u du du′
  lt (u ⨂ v) (inj₁ (du , _)) (inj₂ (_ , dv))  = ⊥
  lt (u ⨂ v) (inj₂ (_ , dv)) (inj₁ (du , _))  = ⊤
  lt (u ⨂ v) (inj₂ (_ , dv)) (inj₂ (_ , dv′)) = lt v dv dv′

  theorem : ∀ {X : Set} → (u : U) → (i o : ⟦ ϑ u ⟧ X × X) → right u i ≡ inj₁ o → lt {X} u (proj₁ o) (proj₁ i)
  theorem 0′ (() , _) o x
  theorem 1′ (() , _) o x
  theorem I (_ , _) o ()
  theorem (u ⨁ v) (inj₁ x , ix) o p with right u (x , ix) | inspect (right u) (x , ix)
  theorem (u ⨁ v) (inj₁ x , ix) .(inj₁ dx , x′) refl | inj₁ (dx , x′) | Reveal_·_is_.[ eq ] = theorem u (x , ix) (dx , x′) eq
  theorem (u ⨁ v) (inj₁ x , ix) o () | inj₂ dx | Reveal_·_is_.[ eq ]
  theorem (u ⨁ v) (inj₂ dv , x) o p with right v (dv , x) | inspect (right v) (dv , x)
  theorem (u ⨁ v) (inj₂ dv , x) .(inj₂ dv′ , x′) refl | inj₁ (dv′ , x′) | Reveal_·_is_.[ eq ] = theorem v (dv , x) (dv′ , x′) eq
  theorem (u ⨁ v) (inj₂ dv , x) o () | inj₂ y | Reveal_·_is_.[ eq ]
  theorem (u ⨂ v) (inj₁ (du , v′) , x) o p with right u (du , x) | inspect (right u) (du , x)
  theorem (u ⨂ v) (inj₁ (du , v′) , x) .(inj₁ (du′ , v′) , x′) refl | inj₁ (du′ , x′) | Reveal_·_is_.[ eq ] = theorem u (du , x) (du′ , x′) eq
  theorem (u ⨂ v) (inj₁ (du , v′) , x) o p | inj₂ y | Reveal_·_is_.[ eq ] with first v v′
  theorem (u ⨂ v) (inj₁ (du , v′) , x) .(inj₂ (y , dv) , x′) refl | inj₂ y | Reveal_·_is_.[ eq ] | just (dv , x′) = tt
  theorem (u ⨂ v) (inj₁ (du , v′) , x) o () | inj₂ y | Reveal_·_is_.[ eq ] | nothing
  theorem (u ⨂ v) (inj₂ (u′ , dv) , x) o p with right v (dv , x) | inspect (right v) (dv , x)
  theorem (u ⨂ v) (inj₂ (u′ , dv) , x) .(inj₂ (u′ , dv′) , x′) refl | inj₁ (dv′ , x′) | Reveal_·_is_.[ eq ] = theorem v (dv , x) (dv′ , x′) eq
  theorem (u ⨂ v) (inj₂ (u′ , dv) , x) o () | inj₂ y | Reveal_·_is_.[ eq ]

  p = I ⨁ (1′ ⨂ (I ⨂ I ⨂ I))

  ten = I ⨂ I ⨂ I ⨂ (I ⨂ I ⨂ I) ⨂ I

  r : ⟦ ten ⟧ Bool
  r = (((false , true) , false) , (true , false) , true) , true

  f : ⟦ p ⟧ Bool
  f = inj₂ (tt , ((false , false) , true))

  z : ⟦ ϑ p ⟧ Bool × Bool
  z = inj₂ (inj₂ (tt , inj₁ (inj₁ (tt , true) , false))) , true

  z′ : ⟦ ϑ p ⟧ Bool -- × Bool
  z′ = inj₂ (inj₂ (tt , inj₂ ((true , true) , tt))) -- , true

  -- prr : lt p z′ z
  -- prr = tt

  mutual
    acc⨁r : ∀ {X : Set} u v x → Acc (lt v) x → WfRec (lt {X} (u ⨁ v)) (Acc (lt (u ⨁ v))) (inj₂ x)
    acc⨁r u v x _ (inj₁ y) ()
    acc⨁r u v x (acc rs) (inj₂ y) p = acc (acc⨁r u v y (rs y p))

    acc⨁l : ∀ {X : Set} u v x → Acc (lt {X} u) x → Well-founded (lt {X} v) → WfRec (lt (u ⨁ v)) (Acc (lt (u ⨁ v))) (inj₁ x)
    acc⨁l u v x (acc rs) wf (inj₁ y) p  = acc (acc⨁l u v y (rs y p) wf)
    acc⨁l u v x (acc rs) wf (inj₂ y) p = acc (acc⨁r u v y (wf y))

    acc⨂r : ∀ {X : Set} u v u′ dv → Acc (lt v) dv →  WfRec (lt {X} (u ⨂ v)) (Acc (lt (u ⨂ v))) (inj₂ (u′ , dv))
    acc⨂r u v x dy _ (inj₁ x₁) ()
    acc⨂r u v x dy (acc rs) (inj₂ (u′ , dv)) p = acc (acc⨂r u v u′ dv (rs dv p))

    acc⨂l : ∀ {X : Set} u v du v′ → Acc (lt (u)) du → Well-founded (lt {X} v) → WfRec (lt {X} (u ⨂ v)) (Acc (lt (u ⨂ v))) (inj₁ (du , v′))
    acc⨂l u v du v′ (acc rs) wf (inj₁ (du′ , v′′)) x = acc (acc⨂l u v du′ v′′ (rs du′ x) wf)
    acc⨂l u v du v′ (acc rs) wf (inj₂ (u′ , dv)) tt = acc (acc⨂r u v u′ dv (wf dv))

    lt-WF : {X : Set} → (u : U) → Well-founded (lt {X} u)
    lt-WF u x = acc (aux u x)
      where aux : ∀ u x → WfRec (lt u) (Acc (lt u)) x
            aux 0′ () y p
            aux 1′ () y p
            aux I tt tt ()
            aux (u ⨁ v) (inj₁ x) (inj₁ y) p  = acc (acc⨁l u v y (lt-WF u y) (lt-WF v))
            aux (u ⨁ v) (inj₁ x) (inj₂ y) p = acc (acc⨁r u v y (lt-WF v y))
            aux (u ⨁ v) (inj₂ y₁) (inj₁ x) ()
            aux (u ⨁ v) (inj₂ x) (inj₂ y) p = acc (acc⨁r u v y (lt-WF v y))
            aux (u ⨂ v) (inj₁ (dx , y)) (inj₁ (dx′ , y′)) p = acc (acc⨂l u v dx′ y′ (lt-WF u dx′) (lt-WF v))
            aux (u ⨂ v) (inj₁ (dx , y)) (inj₂ (x , dy)) tt = acc (acc⨂r u v x dy (lt-WF v dy))
            aux (u ⨂ v) (inj₂ (x , dy)) (inj₁ (dx , y)) ()
            aux (u ⨂ v) (inj₂ (x , dy)) (inj₂ (x′ , dy′)) p = acc (acc⨂r u v x′ dy′ (lt-WF v dy′))

  traverse : ∀ {X : Set} → (u : U) → ⟦ u ⟧ X → List (⟦ ϑ u ⟧ X × X)
  traverse u z with first u z
  traverse u z | nothing = []
  traverse u z | just x  = aux u x (lt-WF u (proj₁ x))
    where aux : {X : Set} → (u : U) → (z : ⟦ ϑ u ⟧ X × X) → Acc (lt {X} u) (proj₁ z) → List (⟦ ϑ u ⟧ X × X)
          aux u z (acc rs) with right u z | inspect (right u) z
          aux u z (acc rs) | inj₁ x | Reveal_·_is_.[ eq ] = z ∷ aux u x (rs (proj₁ x) (theorem u z x eq))
          aux u z (acc rs) | inj₂ _ | _ = z ∷ []

  plug : ∀ {X : Set} → (u : U) → ⟦ ϑ u ⟧ X → X → ⟦ u ⟧ X
  plug 0′ () x
  plug 1′ () x
  plug I tt x = x
  plug (u ⨁ v) (inj₁ u′) x  = inj₁ (plug u u′ x)
  plug (u ⨁ v) (inj₂ v′) x  = inj₂ (plug v v′ x)
  plug (u ⨂ v) (inj₁ (du , v′)) x = plug u du x  , v′
  plug (u ⨂ v) (inj₂ (u′ , dv)) x = u′           , plug v dv x

  Zipper : U → Set
  Zipper u = μ u × List (⟦ ϑ u ⟧ (μ u))

  plug-⊲ : ∀ (u : U) → μ u → List (⟦ ϑ u ⟧ (μ u)) → μ u
  plug-⊲ u t []        = t
  plug-⊲ 0′ t (() ∷ xs)
  plug-⊲ 1′ t (() ∷ xs)
  plug-⊲ I t (tt ∷ xs) = t
  plug-⊲ (u ⨁ v) t (inj₁ du ∷ xs)        = plug-⊲ (u ⨁ v) (In (inj₁ (plug u du t))) xs
  plug-⊲ (u ⨁ v) t (inj₂ dv ∷ xs)        = plug-⊲ (u ⨁ v) (In (inj₂ (plug v dv t))) xs
  plug-⊲ (u ⨂ v) t (inj₁ (du , v′) ∷ xs) = plug-⊲ (u ⨂ v) (In ((plug u du t) , v′)) xs
  plug-⊲ (u ⨂ v) t (inj₂ (u′ , dv) ∷ xs) = plug-⊲ (u ⨂ v) (In (u′ , (plug v dv t))) xs

  plug-⊳ : ∀ (u : U) → μ u → List (⟦ ϑ u ⟧ (μ u)) → μ u
  plug-⊳ u t []       = t
  plug-⊳ 0′ t (() ∷ xs)
  plug-⊳ 1′ t (() ∷ xs)
  plug-⊳ I t (tt ∷ xs)       = t
  plug-⊳ (u ⨁ v) t (inj₁ du ∷ xs)        = In (inj₁ (plug u du (plug-⊳ (u ⨁ v) t xs)))
  plug-⊳ (u ⨁ v) t (inj₂ dv ∷ xs)        = In (inj₂ (plug v dv (plug-⊳ (u ⨁ v) t xs)))
  plug-⊳ (u ⨂ v) t (inj₁ (du , v′) ∷ xs) = In ((plug u du (plug-⊳ (u ⨂ v) t xs)) , v′)
  plug-⊳ (u ⨂ v) t (inj₂ (u′ , dv) ∷ xs) = In (u′ , (plug v dv (plug-⊳ (u ⨂ v) t xs )))

  to-left : (u : U) → μ u → List (Zipper u)
  to-left = {!!}

  Tree : U
  Tree = I ⨂ I ⨁ 1′

  Tree′ = μ Tree

  pattern node l r  = In (inj₁ (l , r))
  pattern leaf      = In (inj₂ tt)

  s : List (⟦ ϑ Tree ⟧ Tree′)
  s = inj₁ (inj₁ (tt , node leaf leaf)) ∷ inj₁ (inj₂ (leaf , tt )) ∷ []


  -- lemma : ∀ u v t xs x → plug-⊲ (u + v) t (xs ++ inj₁ x ∷ []) ≡ plug-⊲ ((u + v)) (In (inj₁ (plug u x t))) xs
  -- lemma u v t [] x = refl
  -- lemma u v t (y ∷ xs) x = {!!}

  -- ⊲-to-⊳ : ∀ (u : U) (s : List (⟦ ϑ u ⟧ (μ u))) (t : μ u) → plug-⊲ u t s ≡ plug-⊳ u t (reverse s)
  -- ⊲-to-⊳ u s t = aux u s (reverseView s) t
  --   where aux : (u : U) (s : List (⟦ ϑ u ⟧ (μ u))) → Reverse s → (t : μ u) → plug-⊲ u t s ≡ plug-⊳ u t (reverse s)
  --         aux u .[] [] t = refl
  --         aux 0′ .(xs ++ _ ∷ []) (xs ∶ rs ∶ʳ ()) t
  --         aux 1′ .(xs ++ _ ∷ []) (xs ∶ rs ∶ʳ ()) t
  --         aux I .(xs ++ tt ∷ []) (xs ∶ rs ∶ʳ tt) t = {!!}
  --         aux (u + v) .(xs ++ inj₁ x ∷ []) (xs ∶ rs ∶ʳ inj₁ x) t
  --           rewrite reverse-++-commute xs (Data.List.[ inj₁ x ]) = {!!}
  --         aux (u + v) .(xs ++ inj₂ y ∷ []) (xs ∶ rs ∶ʳ inj₂ y) t = {!!}
  --         aux (u × v) .(xs ++ inj₁ (du , v′) ∷ []) (xs ∶ rs ∶ʳ inj₁ (du , v′)) t = {!!}
  --         aux (u × v) .(xs ++ inj₂ (u′ , dv) ∷ []) (xs ∶ rs ∶ʳ inj₂ (u′ , dv)) t = {!!}

  -- Rel : ∀ (u : U) → Zipper u → Zipper u → Set
  -- Rel 0′ (In () , s) (t′ , s′)
  -- Rel 1′ (In tt , s) (t′ , s′) = {!!}
  -- Rel I (t , s) (t′ , s′)      = ⊥
  -- Rel (u + v) (t , s) (t′ , s′) = {!!}
  -- Rel (u × u₁) (t , s) (t′ , s′) = {!!}
  -- ⊳-++-inj₁ : (u v : U) → (x : ⟦ ϑ u ⟧ (μ (u + v))) → (s : List (⟦ ϑ u ⟧ (μ (u + v)) ⊎ ⟦ ϑ v ⟧ (μ (u + v))))
  --            → (t : μ (u + v))→ plug-⊲ (u + v) t (s ∷ʳ inj₁ x) ≡ In (x , plug-⊲ u t s)
  -- ⊳-++-inj₁ = ?

  -- subtree : ⟦ ϑ p ⟧ (μ p)
  -- subtree = inj₁ (inj₂ (In (inj₂ tt) , tt))

--   δ I₁        = K₁ ⊤
--   δ (K₁ A)    = K₁ ⊥
--   δ (F +₁ G)   = δ F +₁ δ G
--   δ (F ×₁ G)  = (δ F ×₁ G) +₁ F ×₁ (δ G)
-- \end{code}
-- %</Diff>

--   Zipper : FDesc → Set
--   Zipper F = μ F × List (⟦ δ F ⟧₁ (μ F))

--   plug : (F : FDesc) → Zipper F → μ F
--   plug F (t , [])       = t
--   plug I₁ (t , tt ∷ xs) = t
--   plug (K₁ A) (t , () ∷ xs)
--   plug (F +₁ G) (t , inj₁ x ∷ xs) = μ-in (inj₁ {!!})
--   plug (F +₁ G) (t , inj₂ y ∷ xs) = {!!}
--   plug (F ×₁ G) (t , inj₁ (df , g) ∷ xs) = μ-in ({!plug!} , g)
--   plug (F ×₁ G) (t , inj₂ (proj₁ , proj₂) ∷ xs) = {!!}

  data U₂ : Set where
    0′   :  U₂
    1′   :  U₂
    ↗_   :  U → U₂
    ↘_   :  U → U₂
    _⨁_  : (P Q : U₂)  → U₂
    _⨂_  : (P Q : U₂)  → U₂

  infixl 50 ↗_ ↘_

  Δ : U → U₂
  Δ 0′ = 0′
  Δ 1′ = 0′
  Δ I  = 1′
  Δ (u ⨁ v) = Δ u ⨁ Δ v
  Δ (u ⨂ v) = (Δ u ⨂ ↘ v) ⨁ (↗ u ⨂ Δ v)

  ⟦_⟧₂ : U₂ → (Set → Set → Set)
  ⟦ 0′ ⟧₂ X Y = ⊥
  ⟦ 1′ ⟧₂ X Y = ⊤
  ⟦ ↗ u ⟧₂ X Y = ⟦ u ⟧ X
  ⟦ ↘ u ⟧₂ X Y = ⟦ u ⟧ Y
  ⟦ u ⨁ v ⟧₂ X Y = ⟦ u ⟧₂ X Y ⊎ ⟦ v ⟧₂ X Y
  ⟦ u ⨂ v ⟧₂ X Y = ⟦ u ⟧₂ X Y × ⟦ v ⟧₂ X Y

  plug₂ : {X : Set} → (u : U) → ⟦ Δ u ⟧₂ X X → X → ⟦ u ⟧ X
  plug₂ 0′ () x
  plug₂ 1′ () x
  plug₂ I tt x        = x
  plug₂ (u ⨁ v) (inj₁ du) x = inj₁ (plug₂ u du x)
  plug₂ (u ⨁ v) (inj₂ dv) x = inj₂ (plug₂ v dv x)
  plug₂ (u ⨂ v) (inj₁ (du , v′)) x = plug₂ u du x , v′
  plug₂ (u ⨂ v) (inj₂ (u′ , dv)) x = u′ , plug₂ v dv x
\end{code}
