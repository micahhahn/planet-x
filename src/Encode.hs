module Encode where

import Control.Monad.State.Lazy

import Exp
import Data.Proxy

class Encode a where
    encode :: a -> Int
    decode :: Int -> a
    rank :: Proxy a -> Int

encodeExp :: (Encode a) => Exp a -> [[Int]]
encodeExp e = unpack (normalize e)
    where unpack (Var v) = [[encode v]]
          unpack (Not (Var v)) = [[negate (encode v)]]
          unpack (And l r) = unpack l ++ unpack r
          unpack (Or l r) = [head (unpack l) ++ head (unpack r)]
 
decodeExp :: (Encode a) => [[Int]] -> Exp a
decodeExp is = foldl1 And $ (\as -> foldl1 Or $ decodeVar <$> as) <$> is
    where decodeVar i = if i < 0 then Not . Var . decode . abs $ i else Var . decode . abs $ i

decodeConjunctiveExp :: (Encode a) => [Int] -> Exp a
decodeConjunctiveExp is = foldl1 And $ decodeVar <$> is
    where decodeVar i = if i < 0 then Not . Var . decode . abs $ i else Var . decode . abs $ i

freshVar :: (Encode a) => State Int (Exp a)
freshVar = do
    i <- get
    put $ i + 1
    return . Var . decode $ i