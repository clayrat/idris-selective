module Control.Applicative.Free

import Data.Const

%default total

public export
data FreeAp : (Type -> Type) -> Type -> Type where
  Pure : x -> FreeAp f x
  Ap : f x -> FreeAp f (x -> y) -> FreeAp f y

runAp : Applicative g => (forall x. f x -> g x) -> FreeAp f b -> g b
runAp _ (Pure a) = pure a
runAp f (Ap fa r) = (flip apply) <$> f fa <*> runAp f r

runApM : Monoid m => (forall x. f x -> m) -> FreeAp f b -> m
runApM f = getConst . runAp (\m => MkConst $ f m)

export
liftAp : f a -> FreeAp f a
liftAp x = Ap x (Pure id)

count : FreeAp f a -> Nat
count (Pure _) = Z
count (Ap _ r) = S (count r)

export
Functor (FreeAp f) where
  map f (Pure a)  = Pure (f a)
  map f (Ap fa r) = Ap fa (map (f .) r)

--Applicative (FreeAp f) where
--  pure = Pure
--  Pure f <*> x = map f x
--  Ap fa r <*> x = Ap fa (flip <$> r <*> x)

public export
data FreeApR : (Type -> Type) -> Type -> Type where
  PureR : x -> FreeApR f x
  ApR : f (x -> y) -> FreeApR f x -> FreeApR f y

export
raise : (Functor f, Applicative g) => (forall x. f x -> g x) -> FreeApR f a -> g a
raise k (PureR x) = pure x
raise k (ApR g r) = k g <*> raise k r

export
liftApR : Functor f => f a -> FreeApR f a
liftApR x = ApR (map const x) (PureR ())

export
Functor f => Functor (FreeApR f) where
  map f (PureR a)   = PureR (f a)
  map f (ApR fxy r) = ApR (map (f .) fxy) r

export
Functor f => Applicative (FreeApR f) where
  pure = PureR
  PureR f <*> x = map f x
  ApR fxy r <*> x = ApR (map uncurry fxy) (assert_total $ MkPair <$> r <*> x)