module Data.Const

%default total

public export
record Const (a : Type) (b : Type) where
  constructor MkConst
  getConst : a

export
Functor (Const a) where
  map _ (MkConst x) = MkConst x

export
Monoid m => Applicative (Const m) where
  pure x = MkConst neutral
  (MkConst f) <*> (MkConst x) = MkConst (f <+> x)