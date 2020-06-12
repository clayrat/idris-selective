module Control.Selective

%default total

interface Applicative f => Selective f where
  select : f (Either a b) -> f (a -> b) -> f b

branch : Selective f => f (Either a b) -> f (a -> c) -> f (b -> c) -> f c
branch fe fac fbc = select (select (map (map Left) fe) (map (\ac => Right . ac) fac)) fbc

apS : Selective f => f (a -> b) -> f a -> f b
apS fab fa = select (map Left fab) (map (flip apply) fa)

selectM : Monad f => f (Either a b) -> f (a -> b) -> f b
selectM fe fab = fe >>= \case Left a => map (\ab => ab a) fab
                              Right b => pure b

ifS : Selective f => f Bool -> f a -> f a -> f a
ifS fb ft ff = branch (map (\b => if b then Left () else Right ()) fb) (map const ft) (map const ff)
