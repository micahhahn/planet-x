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

import Data.Bits (shift, (.&.))

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

bindFullVar :: (Encode a, Ord a) => Exp a -> Exp a -> TExp a
bindFullVar trueE falseE = do
    (TseytinState m i) <- get
    let var = Var . decode $ i
    let m' = Map.insert trueE var m
    let m'' = Map.insert falseE (Not var) m'
    put $ TseytinState m'' (i+1)
    return var

simplify :: (Encode a, Ord a) => Exp a -> TExp a
simplify = goClauses . toNNF
    where toNNF :: Exp a -> Exp a
          toNNF e@(Var _) = e
          toNNF (Not (Not x)) = x
          toNNF e@(Not (Var _)) = e
          toNNF (Not (And l r)) = toNNF (Not l) `Or` toNNF (Not r)
          toNNF (Not (Or l r)) = toNNF (Not l) `And` toNNF (Not r)
          toNNF (Not x) = toNNF $ Not (toNNF x)
          toNNF (And l r) = toNNF l `And` toNNF r
          toNNF (Or l r) = toNNF l `Or` toNNF r
          toNNF (Xor l r) = toNNF $ (l `Or` r) `And` (Not l `Or` Not r)
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

simplifyT :: (Encode a, Ord a) => Exp a -> TExp a
simplifyT o@(Var _) = return o
simplifyT o@(Not (Var _)) = return o
simplifyT (Xor l r) = do
    l' <- simplifyT l
    r' <- simplifyT r
    nl' <- simplifyT (Not l)
    nr' <- simplifyT (Not r)
    let trueE = (l' `Or` r') `And` (nl' `Or` nr')
    let falseE = (l' `Or` nr') `And` (nl' `Or` r')
    bindFullVar trueE falseE
simplifyT x = return x

data BoundExpressions a = BoundExpressions [Exp a] Int

equivVar :: (Encode a) => Exp a -> Exp a -> State (BoundExpressions a) (Exp a)
equivVar trueE falseE = do
    (BoundExpressions es i) <- get
    let var = Var . decode $ i
    let trueI = var `Imp` trueE
    let falseI = Not var `Imp` falseE
    put $ BoundExpressions (trueI : falseI : es) (i+1)
    return var

bindAnd :: (Encode a) => Exp a -> Exp a -> State (BoundExpressions a) (Exp a)
bindAnd l r = equivVar (l `And` r) (Not l `Or` Not r)

bindXor :: (Encode a) => Exp a -> Exp a -> State (BoundExpressions a) (Exp a)
bindXor l r = equivVar ((l `Or` r) `And` (Not l `Or` Not r)) ((l `Or` Not r) `And` (Not l `Or` r))

-- 1 if at least two of three inputs is true
bindCarry :: (Encode a) => Exp a -> Exp a -> Exp a -> State (BoundExpressions a) (Exp a)
bindCarry x1 x2 x3 = equivVar trueE falseE
    where trueE = (x1 `Or` x2) `And` (x2 `Or` x3) `And` (x1 `Or` x3)
          falseE = (Not x1 `Or` Not x2) `And` (Not x2 `Or` Not x3) `And` (Not x1 `Or` Not x3)

countFull :: (Encode a) => [Exp a] -> State (BoundExpressions a) [Exp a]
countFull es = goCount es

    where adder :: (Encode a) => [Exp a] -> [Exp a] -> State (BoundExpressions a) [Exp a]
          adder [l] [] = return [l]
          adder [] [r] = return [r]
          adder [l] [r] = halfAdder l r
          adder (l:ls) (r:rs) = do
              as <- halfAdder l r
              case as of
                  [a, c] -> (a:) <$> fAdder ls rs c
          
          fAdder [] [] c = return [c]
          fAdder [l] [] c = halfAdder l c
          fAdder [] [r] c = halfAdder r c
          fAdder (l:ls) (r:rs) c = do
              as <- fullAdder l r c
              case as of
                [a, c'] -> (a:) <$> fAdder ls rs c

          halfAdder :: (Encode a) => Exp a -> Exp a -> State (BoundExpressions a) [Exp a]
          halfAdder l r = liftM2 (\a c -> [a, c]) (bindXor l r) (bindAnd l r)

          fullAdder :: (Encode a) => Exp a -> Exp a -> Exp a -> State (BoundExpressions a) [Exp a]
          fullAdder l r c = liftM2 (\a c -> [a, c]) (bindXor l r >>= bindXor c) (bindCarry l r c)

          goCount :: (Encode a) => [Exp a] -> State (BoundExpressions a) [Exp a]
          goCount [e] = return [e]
          goCount es = do
              let half = length es `div` 2
              lc <- goCount $ take half es
              rc <- goCount $ drop half es
              adder lc rc

kEQ' :: (Encode a) => [Exp a] -> Int -> State (BoundExpressions a) (Exp a)
kEQ' es n = do
    bs <- countFull es
    return $ allOf [ (if (shift n (-i) .&. 1) == 1 then b else Not b) | (b, i) <- zip bs [0..] ]

xs = [ Var (VarX PlanetX i) | i <- [1..18]]

showB :: forall a. (Encode a) => State (BoundExpressions a) (Exp a) -> Exp a
showB c = allOf (e : es)
    where (e, BoundExpressions es _) = runState c (BoundExpressions [] (rank (Proxy :: Proxy a) + 1))

-- { X1, X2, X3, X4 }
-- v1 => (X1 | X2) & (X3 | X4)
-- v2 => (X1 | X3) & (X2 | X4)
-- v3 => (!X1 | !X2) & (!X3 | !X4)
-- v4 => (!X1 | !X3) & (!X2 | !X4)
--  0 : !X1 & !X2 & !X3 & !X4
-- >0 : X1 | X2 | X3 | X4
-- >1 : v1 | v2
-- >2 : !(v3 | v4)
--  4 :  X1 & X2 & X3 & X4
-- <4 : !X1 | !X2 | !X3 | !X4
-- <3 : v3 | v4
-- <2 : !(v1 | v2)
-- <1 : !X1 & !X2 & !X3 & !X4

-- { X1, X2, X3, X4, X5 }
-- x1 => (X1 | X2 | X3) & (X4 | X5)
-- x2 => (X1 | X2 | X4) & (X3 | X5)

-- { X1, X2, X3, X4, X5, X6, X7, X8 }
-- v1 => (X1 | X2 | X3 | X4) & (X5 | X6 | X7 | X8)
-- v2 => (X1 | X2 | X7 | X8) & (X3 | X4 | X5 | X6)
-- v3 => (X1 | X3 | X5 | X7) & (X2 | X4 | X6 | X8)

-- v1 => (X1 | X2 | X3) & (X4 | X5 | X6) & (X7 | X8)
-- v2 => (X1 | X4 | X7) & (X2 | X5 | X8) & (X3 | X6)


showC :: forall a. (Encode a) => TExp a -> Exp a
showC c = allOf (e : [v `Imp` e' | (e', v) <- Map.assocs es ])
    where (e, TseytinState es _) = runState c (TseytinState Map.empty (rank (Proxy :: Proxy a) + 1))