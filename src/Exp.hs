{-# LANGUAGE StandaloneDeriving #-}

module Exp where

import Control.Monad.State.Lazy

-- Represents an expression in first order logic
data Exp a = Var a
           | Not (Exp a)
           | And (Exp a) (Exp a)
           | Or (Exp a) (Exp a)
           | Imp (Exp a) (Exp a) 

deriving instance (Eq a) => Eq (Exp a)

instance (Show a) => Show (Exp a) where
    show e = case e of
        Var x -> show x

        Not v@(Var _) -> "!"  ++ show v
        Not v@(Not _) -> "!"  ++ show v
        Not x         -> "!" ++ wrap x

        Imp p q -> let f = \p -> case p of
                                     i@(Imp _ _) -> wrap i
                                     i@(And _ _) -> wrap i
                                     i@(Or _ _) -> wrap i
                                     x -> show x
                    in f p ++ " => " ++ f q
    
        And l r -> let f = \x -> case x of
                                     o@(Or _ _) -> wrap o
                                     i@(Imp _ _) -> wrap i
                                     x -> show x
                    in f l ++ " & " ++ f r
        
        Or l r ->  let f = \x -> case x of
                                     a@(And _ _) -> wrap a
                                     i@(Imp _ _) -> wrap i
                                     x -> show x
                    in f l ++ " | " ++ f r

        where wrap = ("(" ++) . (++ ")") . show

-- Converts an expression to CNF form
normalize :: Exp a -> Exp a
normalize = toCNF . toNNF

    where toNNF :: Exp a -> Exp a
          toNNF v@(Var _) = v
          toNNF (Not (Not x)) = x
          toNNF (Not (Var s)) = Not (Var s)
          toNNF (Not (And l r)) = (toNNF $ Not l) `Or` (toNNF $ Not r)
          toNNF (Not (Or l r)) = (toNNF $ Not l) `And` (toNNF $ Not r)
          toNNF (And l r) = (toNNF l) `And` (toNNF r)
          toNNF (Or l r) = (toNNF l) `Or` (toNNF r)
          toNNF (Imp p q) = (toNNF $ Not p) `Or` (toNNF q)

          toCNF v@(Var _) = v
          toCNF (Not v@(Var _)) = Not v
          toCNF (Not _) = error "Expression not in NNF"
          toCNF (And l r) = And (toCNF l) (toCNF r)
          toCNF (Or l r) = case toCNF l of
                               And al ar -> (toCNF (al `Or` r)) `And` (toCNF (ar `Or` r))
                               x -> case toCNF r of
                                        And rl rr -> (toCNF (x `Or` rl)) `And` (toCNF (x `Or` rr))
                                        y -> x `Or` y
          toCNF (Imp _ _) = error "Expression not in NNF"