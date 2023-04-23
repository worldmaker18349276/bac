module BAC.Fundamental.Mutation (
  Mutation (..),
) where

import BAC.Base

-- | A mark indicating mutations of symbols.
data Mutation =
    Transfer  [(Symbol, Symbol)] [(Symbol, Symbol)]
  | Duplicate  (Symbol, Symbol)  [(Symbol, Symbol)]
  | Merge     [(Symbol, Symbol)]  (Symbol, Symbol)
  | Delete     (Symbol, Symbol)
  | Insert                        (Symbol, Symbol)
