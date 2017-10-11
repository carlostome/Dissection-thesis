{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternSynonyms #-}
module Dissection where

  import Data.Bifunctor

  {- Functors -}

  data Void

  data Unit = Unit

  -- identity functor
  newtype Id x = Id x

  instance Functor Id where
    fmap f (Id x) = Id (f x)

  -- Konstant functor
  newtype K a x = K a

  instance Functor (K a) where
    fmap _ (K a) = K a

  -- Sum functor
  data (f :+: g) x = L (f x) | R (g x)

  instance (Functor f, Functor g) => Functor (f :+: g) where
    fmap f (L fx) = L $ fmap f fx
    fmap f (R gx) = R $ fmap f gx

  -- Product functor
  data (f :*: g) x = P (f x)  (g x)

  instance (Functor f, Functor g) => Functor (f :*: g) where
    fmap f (P fx gx) = P (fmap f fx) (fmap f gx)

  infixr 6 :+:
  infixr 7 :*:

  -- Fixpoint of a functor
  newtype Fix f = Fix { unFix :: f (Fix f) }

 {- Bifunctors -}

  newtype Fst x y  = Fst x

  instance Bifunctor Fst where
    bimap f _ (Fst x) = Fst (f x)

  newtype Snd x y  = Snd y

  instance Bifunctor Snd where
    bimap _ g (Snd y) = Snd (g y)

  newtype K2 a x y = K2 a

  instance Bifunctor (K2 a) where
    bimap _ _ (K2 a) = K2 a

  newtype Clown f x y = Clown (f x)

  instance Functor f => Bifunctor (Clown f) where
    bimap f _ (Clown fx) = Clown (fmap f fx)

  newtype Joker f x y = Joker (f y)

  instance Functor f => Bifunctor (Joker f) where
    bimap _ g (Joker fy) = Joker (fmap g fy)

  data (f :++: g) x y = L2 (f x y) | R2 (g x y)

  instance (Bifunctor f, Bifunctor g) => Bifunctor (f :++: g) where
    bimap f g (L2 fxy) = L2 (bimap f g fxy)
    bimap f g (R2 gxy) = R2 (bimap f g gxy)

  data (f :**: g) x y = P2 (f x y) (g x y)

  instance (Bifunctor f, Bifunctor g) => Bifunctor (f :**: g) where
    bimap f g (P2 fxy gxy) = P2 (bimap f g fxy) (bimap f g gxy)

  infixr 6 :++:
  infixr 7 :**:

  class (Functor p, Bifunctor pd) => Dissect p pd | p -> pd where
    right :: Either (p j) (pd c j,c) -> Either (j,pd c j) (p c)

  instance Dissect Id (K2 ()) where
    right x = case x of
      Left (Id j )     -> Left (j , K2 ())
      Right (K2 (), c) -> Right (Id c)

  instance Dissect (K a) (K2 Void) where
    right (Left (K a))      = Right (K a)
    right (Right (K2 z ,c)) = undefined

  instance (Dissect g gd, Dissect f fd) => Dissect (f :+: g) (fd :++: gd) where
    right x =  case x of
      Left (L pj) -> mindp (right (Left pj ))
      Left (R qj) -> mindq (right (Left qj ))
      Right (L2 pd , c) -> mindp (right (Right (pd , c)))
      Right (R2 qd , c) -> mindq (right (Right (qd , c)))
      where
        mindp (Left (j , pd))  = Left  (j , L2 pd )
        mindp (Right pc)       = Right (L pc)
        mindq (Left (j , qd )) = Left (j , R2 qd )
        mindq (Right qc)       = Right (R qc)

  instance (Dissect p pd, Dissect q qd) =>
    Dissect (p :*: q) (pd :**: Joker q :++: Clown p :**: qd) where
      right x = case x of
       Left (P pj qj) -> mindp (right (Left pj)) qj
       Right (L2 (P2 pd (Joker qj)), c) -> mindp (right (Right (pd , c))) qj
       Right (R2 (P2 (Clown pc) qd), c) -> mindq pc (right (Right (qd , c)))
       where
         mindp (Left (j , pd )) qj = Left (j , L2 (P2 pd (Joker qj) ))
         mindp (Right pc) qj       = mindq pc (right (Left qj ))
         mindq pc (Left (j , qd )) = Left (j , R2 (P2 (Clown pc)  qd ))
         mindq pc (Right qc)       = Right (P pc qc)


  tcata :: Dissect p pd => (p a -> a) -> Fix p -> a
  tcata phi t = load phi t []

  load :: Dissect p pd => (p v -> v) -> Fix p -> [pd v (Fix p)] -> v
  load phi (Fix pt) stk = next phi (right (Left pt)) stk

  next :: Dissect p pd => (p v -> v) -> Either (Fix p, pd v (Fix p)) (p v)
       -> [pd v (Fix p)] -> v
  next phi (Left (t , pd)) stk = load phi t (pd : stk)
  next phi (Right pv)      stk = unload phi (phi pv) stk

  unload :: Dissect p pd => (p v -> v) -> v -> [pd v (Fix p)] -> v
  unload phi v [] = v
  unload phi v (pd : stk) = next phi (right (Right (pd,v))) stk

  type Bin a = Fix (K a :+: Id :*: Id)

  pattern Node :: Bin a -> Bin a -> Bin a
  pattern Node l r = Fix (R (P (Id l) (Id r)))

  pattern Leaf :: a -> Bin a
  pattern Leaf x = Fix (L (K x))

  eval :: Bin Int -> Int
  eval = tcata phi
    where
      phi :: (K Int :+: Id :*: Id) Int -> Int
      phi (L (K x))             = x
      phi (R (P (Id l) (Id r))) = l + r

  plug :: Dissect p pd => [pd v (Fix p)] -> (v -> Fix p) -> Fix p -> Fix p
  plug [] embed t         = t
  plug (pd : stk) embed t = undefined

  -- class Reducible x where
  --   isRedex :: x -> Bool

  -- instance Reducible (K a x) where
  --   isRedex _ = False

  -- instance Reducible x => Reducible (Id x) where
  --   isRedex (Id x) = isRedex x

  -- instance (Reducible (f x), Reducible (g x)) => Reducible ((f :+: g) x) where
  --   isRedex (L fx) = isRedex fx
  --   isRedex (R fx) = isRedex fx

  -- instance (Reducible (f x), Reducible (g x)) => Reducible ((f :*: g) x) where
  --   isRedex (P fx gy) = not (isRedex fx) && not (isRedex gy)

  -- isFixRedex :: Reducible f => Fix f -> Bool
  -- isFixRedex (Fix f) = isRedex f
  decompose :: Dissect p pd => (p v -> v) -> Fix p
            -> Either (p v, [pd v (Fix p)]) v
  decompose phi t = decompose_term phi t []

  decompose_term :: Dissect p pd => (p v -> v) -> Fix p 
                 -> [pd v (Fix p)] -> Either (p v, [pd v (Fix p)]) v

  decompose_term phi (Fix pt) stk = next1 (right (Left pt)) stk

  next1 :: Dissect p pd => Either (Fix p, pd v (Fix p)) (p v)
        -> [pd v (Fix p)] -> Either (p v, [pd v (Fix p)]) v
  next1 (Left (t , pd)) stk = load1 t (pd : stk)
  next1 (Right pv)      stk = unload1 (phi pv) stk

  unload1 :: Dissect p pd => v -> [pd v (Fix p)] -> Either (p v, [pd v (Fix p)]) v
  unload1 v []         = Right v
  unload1 v (pd : stk) = next1 (right (Right (pd,v))) stk
