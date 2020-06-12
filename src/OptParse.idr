module OptParse

import Data.Const
import Data.Strings
import Control.Applicative.Free

record Option (a : Type) where
  constructor MkOption
  optName : String
  optDefault : Maybe a
  optReader : String -> Maybe a

Functor Option where
  map f (MkOption n d r) = MkOption n (map f d) (map f . r)

parserDefault : FreeApR Option a -> Maybe a
parserDefault = raise optDefault

allOptions : FreeApR Option a -> List String
allOptions = getConst . raise f
  where
  f : Option b -> Const (List String) b
  f opt = MkConst [optName opt]

matchOpt : String -> String -> FreeApR Option a -> Maybe (FreeApR Option a)
matchOpt _   _     (PureR _ ) = Nothing
matchOpt opt value (ApR g x)  =
  if opt == (strCons '-' $ strCons '-' (optName g))
    then map (<$> x) (optReader g value)
    else map (ApR g) (matchOpt opt value x)

runParser : FreeApR Option a -> List String -> Maybe a
runParser p []                 = parserDefault p
runParser p (opt::value::args) = do q <- matchOpt opt value p
                                    runParser q args
runParser _ _                  = Nothing

-- example

record User where
  constructor MkUser
  username : String
  fullname : String
  id : Int

userP : FreeApR Option User
userP = MkUser <$> liftApR (MkOption "username" Nothing Just)
               <*> liftApR (MkOption "fullname" (Just "") Just)
               <*> liftApR (MkOption "id" Nothing parsePositive)
