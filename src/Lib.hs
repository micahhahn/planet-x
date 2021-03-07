{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}

module Lib
    ( someFunc
    ) where

import Control.Monad.Loops (iterateWhile)
import Control.Monad.State.Lazy
import Data.Coerce
import Data.List (intercalate, sort, nub)
import Data.Proxy
import SAT.Mios

import Encode
import Exp
import Logic
import PlanetX

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)

{- solve :: forall a. (Encode a) => State Int (Exp a) -> IO (Exp a)
solve s = do
    let (e, i) = runState s (rank (Proxy :: Proxy a))
    let cnf = encodeExp e
    let desc = CNFDescription (rank (Proxy :: Proxy a) + i - 1) (length cnf) ""
    results <- solveSAT desc cnf
    return $ decodeExp [results] -}

solveAll :: forall a. (Encode a) => State Int (Exp a) -> IO [Exp a]
solveAll s = do
    is <- go 0 (encodeExp e)
    return $ decodeConjunctiveExp <$> is
 
    where varRank = rank (Proxy :: Proxy a)
          (e, i) = runState s (varRank + 1)
        
          go :: Int -> [[Int]] -> IO [[Int]]
          go ix clauses = if ix == 1000
                          then return []
                          else do
              sol <- solveSAT (CNFDescription (i - 1) (length clauses) "") clauses
              case sol of
                  [] -> return []
                  vs -> let vars = take varRank vs
                            newClauses = (negate <$> vars) : clauses
                         in (vars:) <$> go (ix+1) newClauses

testVars = 4

data VarTest = VarTest Int

instance Show VarTest where
    show (VarTest i) = if i > testVars then "v" ++ show i else "V" ++ show i

instance Encode VarTest where
    encode (VarTest i) = i
    decode i = VarTest i
    rank _ = testVars

vars = Var . VarTest <$> [1..testVars]

andM = liftM2 And

clause' = sectorUniqueE `andM` astroidE `andM` dwarfPlanetE `andM` cometE `andM` planetXE `andM` gasCloudE
clause = clause'

game1 = clause `andM` 
        survey Astroid (1, 9) 1 `andM`
        survey DwarfPlanet (5, 11) 2 `andM`
        survey Astroid (5, 10) 2 `andM`
        survey Comet (11, 17) 0 `andM`
        survey Astroid (14, 17) 1 `andM`
        survey Astroid (17, 5) 2  `andM`
        survey DwarfPlanet (17, 5) 3

xNotAdjTo :: Object -> Exp VarX
xNotAdjTo o = foldl1 And $ (\i -> Var (VarX PlanetX i) `Imp` Not (Var (VarX o (prev i)) `Or` Var (VarX o (next i)))) <$> [1..sectorCount]

game2 = foldl1 andM [ clause
                    , survey DwarfPlanet (3, 9) 3
                    , survey Astroid (4, 10) 2
                    , survey DwarfPlanet (7, 13) 0
                    , survey Astroid (9, 15) 2
                    , survey Comet (11, 17) 0
                    , survey Astroid (11, 17) 1
                    , survey Comet (13, 3) 1
                    , survey EmptySpace (3, 4) 0
                    , return (xNotAdjTo EmptySpace)
                    , return (xNotAdjTo GasCloud)
                    ]

writeSatFile :: forall a. (Encode a) => State Int (Exp a) -> String -> IO ()
writeSatFile s f = do
    let varRank = rank (Proxy :: Proxy a)
    let (e, i) = runState s (varRank + 1)
    let iss = encodeExp e
    let x = intercalate "\n" $ (\is -> intercalate " " $ fmap show is) <$> iss
    writeFile f x

showClause :: forall a. (Encode a) => State Int (Exp a) -> Exp a
showClause c = evalState c (rank (Proxy :: Proxy a) + 1)

pretty :: (Show a) => [Exp a] -> IO ()
pretty = mapM_ (putStrLn . unwords . go)
    where go (And l r) = go l ++ go r
          go (Not _) = []
          go (Var v) = [show v]

someFunc :: IO ()
someFunc = do
    asg <- solveAll clause
    print (length asg)

data TseytinState a = TseytinState (Map (Exp a) (Exp a)) Int

type TExp a = State (TseytinState a) (Exp a)

-- Takes an expression and binds it to a fresh unique variable
bindVar :: (Encode a, Ord a) => Exp a -> TExp a
bindVar e = do
    (TseytinState m i) <- get
    case Map.lookup e m of
        Just e' -> return e'
        Nothing -> do
                   let var = Var . decode $ i
                   let m' = Map.insert e var m
                   put $ TseytinState m' (i+1)
                   return var

simplify :: (Encode a, Ord a) => Exp a -> TExp a
simplify = goClauses . toNNF
    where toNNF :: Exp a -> Exp a
          toNNF e@(Var _) = e
          toNNF (Not (Not x)) = x
          toNNF e@(Not (Var _)) = e
          toNNF (Not (And l r)) = toNNF (Not l) `Or` toNNF (Not r)
          toNNF (Not (Or l r)) = toNNF (Not l) `And` toNNF (Not r)
          toNNF (And l r) = toNNF l `And` toNNF r
          toNNF (Or l r) = toNNF l `Or` toNNF r
          toNNF (Imp p q) = toNNF (Not p) `Or` toNNF q
          toNNF (Equiv p q) = toNNF $ (p `Imp` q) `And` (q `Imp` p)
        
          goClauses :: (Encode a, Ord a) => Exp a -> TExp a
          goClauses (And l r) = liftM2 And (goClauses l) (goClauses r)
          goClauses e@(Or _ _) = goClause e
          goClauses e = return e

          goClause :: (Encode a, Ord a) => Exp a -> TExp a
          goClause (Or l r) = liftM2 Or (goClause l) (goClause r)
          goClause e@(And _ _) = goClauses e >>= bindVar
          goClause e = return e

xs = [ Var (VarX PlanetX i) | i <- [1..18]]

showC :: forall a. (Encode a) => TExp a -> Exp a
showC c = allOf (e : [v `Imp` e' | (e', v) <- Map.assocs es ])
    where (e, TseytinState es _) = runState c (TseytinState Map.empty (rank (Proxy :: Proxy a) + 1))