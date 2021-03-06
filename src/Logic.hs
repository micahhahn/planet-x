{-# LANGUAGE ScopedTypeVariables #-}

module Logic where

import Control.Monad.State.Lazy

import Data.Bits (shift, (.&.))
import Data.List (partition)
import Data.Proxy
import Encode
import Exp

anyOf :: [Exp a] -> Exp a
anyOf = foldl1 Or

allOf :: [Exp a] -> Exp a
allOf = foldl1 And

mapTail :: (a -> [a] -> b) -> [a] -> [b]
mapTail _ [] = []
mapTail f (a:as) = f a as : mapTail f as

choose :: [x] -> Int -> [[x]]
choose _ 0 = [[]]
choose [] _ = []
choose xs n = concat $ (\x xs' -> (x :) <$> choose xs' (n - 1) ) `mapTail` xs

mkBinaryAuxVars :: (Encode a) => Int -> State Int [Exp a]
mkBinaryAuxVars i = mapM (const freshVar) [1..bitCount]
    where bitCount = ceiling . logBase 2 . fromIntegral $ i

-- Guarantees that at most one of input expressions is true
binaryAMO :: (Encode a) => [Exp a] -> State Int (Exp a)
binaryAMO exps = do
    binaryAuxVars <- mkBinaryAuxVars (length exps)
    return . foldl1 And $ (\(e, ei) -> foldl1 And $ (\(b, bi) -> mkImp e ei b bi) <$> (zip binaryAuxVars [0..])) <$> (zip exps [0..])

    where mkImp :: Exp a -> Int -> Exp a -> Int -> Exp a
          mkImp e ei b bi = if (shift 1 bi) .&. ei == shift 1 bi then e `Imp` b else e `Imp` (Not b)

-- Guarantees that at least one of the input expressions is true
binaryALO :: (Encode a) => [Exp a] -> State Int (Exp a)
binaryALO exps = do
    binaryAuxVars <- mkBinaryAuxVars (length exps)
    let is = [0..] :: [Int]

    let mkBinary i = foldl1 And $ (\(b, bi) -> if (shift 1 bi) .&. i == shift 1 bi then b else (Not b)) <$> (zip binaryAuxVars is)

    let implications = foldl1 And $ (\(e, ei) -> (mkBinary ei) `Imp` e) <$> (zip exps is)
    
    let unusedBinary = (shift 1 (length binaryAuxVars)) - (length exps)
    let forcing = foldl1 And $ Not . mkBinary <$> take unusedBinary [(length exps)..]

    return $ implications `And` forcing

-- Guarantees that exactly one of the input expressions is true
binaryEO :: (Encode a) => [Exp a] -> State Int (Exp a)
binaryEO exps = do
    amo <- binaryAMO exps
    alo <- binaryALO exps
    return $ amo `And` alo

data ExpSize = ExpSize
             { _auxVars :: Int
             , _clauses :: Int
             , _ops :: Int
             } deriving (Show)

-- Splits a list into even and odd elements
paritySplit :: [a] -> ([a], [a])
paritySplit es = (snd <$> ls, snd <$> rs)
    where (ls, rs) = partition ((== 0) . (`mod` 2) . fst) (zip [0..] es)

sorted :: forall a. (Encode a) => [Exp a] -> State Int ([Exp a], [Exp a])
sorted es = case es of 
    [] -> return ([], [])
    e:[] -> return ([e], [])
    es' ->  do
        let half = length es' `div` 2
        (left, les) <- sorted $ take half es'
        (right, res) <- sorted $ drop half es'
        (merge, mes) <- merge left right
        return (merge, les ++ res ++ mes)
    
    where merge :: [Exp a] -> [Exp a] -> State Int ([Exp a], [Exp a])
          merge [] rs = return (rs, [])
          merge ls [] = return (ls, [])
          merge (l:[]) (r:[]) = do
              x0 <- freshVar
              x1 <- freshVar
              return ([x0, x1], [(l `Or` r) `Imp` x0, x0 `Imp` (l `Or` r), (l `And` r) `Imp` x1, x1 `Imp` (l `And` r)])
          merge ls rs = do
              let (le, lo) = paritySplit ls
              let (re, ro) = paritySplit rs
              (evens, ees) <- merge le re
              (odds, oes) <- merge lo ro
              (merges, mes) <- mergeGo True (tail evens) odds
              return $ (head evens : merges, ees ++ oes ++ mes) 
 
          mergeGo _ [] [] = return ([], [])
          mergeGo _ (even:[]) [] = return ([even], []) 
          mergeGo _ [] (odd:[]) = return ([odd], []) 
          mergeGo True (e:es) (o:os) = do
              v <- freshVar
              (vs, es) <- mergeGo False (e:es) (o:os)
              return (v : vs, v `Imp` (e `Or` o) : (e `Or` o) `Imp` v : es)
          mergeGo False (e:es) (o:os) = do
              v <- freshVar
              (vs, es) <- mergeGo True es os
              return (v : vs, v `Imp` (e `And` o) : (e `And` o) `Imp` v : es)

kEQ :: (Encode a) => [Exp a] -> Int -> State Int (Exp a)
kEQ es k | k == 0         = return $ foldl1 And (Not <$> es)
         | k == length es = return $ foldl1 And es
         | otherwise      = do
            (vs, es') <- sorted es
            let e = (vs !! (k - 1)) `And` Not (vs !! k)
            return . foldl1 And $ e : es'

kNEQ :: (Encode a) => [Exp a] -> Int -> State Int (Exp a)
kNEQ es k = do
    (vs, es) <- sorted es
    let e = if k < length es 
            then (Not $ vs !! (k - 1)) `Or` (vs !! k)
            else last vs
    return . foldl1 And $ e : es

kLT :: (Encode a) => [Exp a] -> Int -> State Int (Exp a)
kLT = undefined

kLEQ :: (Encode a) => [Exp a] -> Int -> State Int (Exp a)
kLEQ = undefined

kGT :: (Encode a) => [Exp a] -> Int -> State Int (Exp a)
kGT = undefined

kGTE :: (Encode a) => [Exp a] -> Int -> State Int (Exp a)
kGTE = undefined

expSize :: forall a. (Encode a) => State Int (Exp a) -> ExpSize
expSize es = ExpSize (i - rank (Proxy :: Proxy a) - 1) (goC e') (goO e')
    where (e, i) = runState es (rank (Proxy :: Proxy a) + 1)
          e' = normalize e

          goO (Not e) = goO e + 1
          goO (l `And` r) = goO l + goO r + 1
          goO (l `Or` r) = goO l + goO r + 1
          goO _ = 0 

          goC (l `And` r) = goC l + goC r + 1
          goC _ = 0



{-
greaterThanEqual :: Object -> Int -> Exp
greaterThanEqual o n = foldl1 And $ (\ss -> foldl1 Or $ (\s -> Var $ SatVar o s True) <$> ss) <$> sectors
    where sectors = choose [1..sectorCount] (sectorCount - n)

lessThanEqual :: Object -> Int -> Exp
lessThanEqual o n = foldl1 And $ (\ss -> foldl1 Or $ (\s -> Not . Var $ SatVar o s True) <$> ss) <$> sectors
    where sectors = choose [1..sectorCount] n
-}