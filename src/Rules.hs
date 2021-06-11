module Rules where

import Data.Word (Word64)
import Data.Vector (Vector)
import qualified Data.Vector as V
import Data.Bits
import Data.Maybe (mapMaybe)

import PlanetX

newtype Solution = Solution { unSolution :: Word64 }
    deriving (Show)

data Tree a = Tree a [Tree a]
            deriving Show

objects :: [[Object]]
objects = fmap (uncurry replicate) [(2, Comet), (4, Astroid), (4, DwarfPlanet), (2, GasCloud), (6, EmptySpace)]

packSolution :: Vector Object -> Solution
packSolution = Solution . foldr (\o w -> shiftL w 3 .|. fromIntegral (fromEnum o)) 0

unpackSolution :: Solution -> Vector Object
unpackSolution (Solution w) = V.fromList $ fmap (\i -> toEnum . fromIntegral $ shiftR w (3 * i) .&. 7) [0..17]

combo :: [[a]] -> [[a]]
combo = f []
    where f :: [[a]] -> [[a]] -> [[a]]
          f _ [] = []
          f [] [[x]] = [[x]]
          f ls ([]:rs) = f ls rs
          f ls ((c:cs):rs) = fmap (c:) (f [] ((cs:ls) ++ rs)) ++ f ((c:cs):ls) rs

combo' :: [[a]] -> [Tree a]
combo' = f []
    where f :: [[a]] -> [[a]] -> [Tree a]
          f _ [] = []
          f [] [[x]] = [Tree x []]
          f ls ([]:rs) = f ls rs
          f ls ((c:cs):rs) = Tree c (f [] ((cs:ls) ++ rs)) : f ((c:cs):ls) rs

mapTree :: (Int -> [a] -> b) -> [Tree a] -> [b]
mapTree f ts = 
    mapTreeInternal :: Int -> [a] -> [b]


-- Range: [-8, 9]
dist :: (Num a, Ord a) => a -> a -> a
dist i1 i2 = wrap (i2 - i1)
    where wrap i
             | i < -8 = i + 18
             | i > 9 = i - 18
             | otherwise = i

isValid :: Vector Object -> Maybe Solution
isValid os = if and (V.imap f os) then Just (packSolution os) else Nothing
    where wrapIndex i
            | i == -1 = 17
            | i == 18 = 0
            | otherwise = i
          f i o = case o of
                    Comet -> (i + 1) == 2 || (i + 1) == 3 || (i + 1) == 5 || (i + 1) == 7 || (i + 1) == 11 || (i + 1) == 13 || (i + 1) == 17
                    Astroid -> os V.! wrapIndex (i - 1) == Astroid || os V.! wrapIndex (i + 1) == Astroid
                    DwarfPlanet -> abs (minimum dists) + maximum dists + 1 == 6
                        where dists = V.imap (\i' o' -> if o' == DwarfPlanet then dist i i' else 0) os
                    EmptySpace -> True
                    GasCloud -> os V.! wrapIndex (i - 1) == EmptySpace || os V.! wrapIndex (i + 1) == EmptySpace
                    PlanetX -> os V.! wrapIndex (i - 1) /= DwarfPlanet && os V.! wrapIndex (i + 1) /= DwarfPlanet

validSolutions = mapMaybe (isValid . V.fromList) (combo objects)