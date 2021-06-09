{-# LANGUAGE TupleSections #-}

module Gen (
    solutions
) where 

import PlanetX
import Logic
import Data.List ((\\), sortBy)
import Data.Word (Word64)
import Data.Bits

type SolutionBuilder = ([(Int, Object)], [Int])

modSector :: Int -> Int
modSector i 
    | i > 18 = i - 18
    | otherwise = i

nextSector :: Int -> Int
nextSector i = modSector (i + 1)

chooseDwarfPlanets :: [Int] -> [[Int]]
chooseDwarfPlanets = concatMap mk 
    where mk i = (i:) . (++ [modSector (i + 5)]) <$> choose (modSector <$> [(i + 1) .. (i + 4)]) 2

chooseAstroids :: [Int] -> [[Int]]
chooseAstroids is = astroids
    where pairs = zip is . drop 1 . cycle $ is 
          adjPairs = [ v | v@(l, r) <- pairs, nextSector l == r ]
          astroids = [ [l1, r1, l2, r2] | [(l1, r1), (l2, r2)] <- choose adjPairs 2, r1 /= l2 && r2 /= l1 ]

chooseComets ::[Int] -> [[Int]]
chooseComets is = comets
    where validIs = filter (\i -> i == 2 || i == 3 || i == 5 || i == 7 || i == 11 || i == 13 || i == 17) is
          comets = choose validIs 2

chooseGasClouds :: [Int] -> [[Int]]
chooseGasClouds is = gasClouds
    where triples = zip3 (drop (length is - 1) . cycle $ is) is (drop 1 . cycle $ is)
          triples' = [v | v@(l, c, r) <- triples, nextSector l == c || nextSector c == r]
          gasClouds = [ [c1, c2] | [(l1, c1, _), (_, c2, r2)] <- choose triples' 2, nextSector c1 /= c2 || (nextSector l1 == c1 && nextSector c2 == r2) ]

stitch :: Object -> ([Int] -> [[Int]]) -> SolutionBuilder -> [SolutionBuilder]
stitch o f (objs, is) = fmap (\ds -> (objs ++ fmap (, o) ds, is \\ ds) ) (f is)

solutions :: [[Object]]
solutions = fmap snd . sortBy (\i1 i2 -> compare (fst i1) (fst i2)) <$> indexSolutions
    where dwarfs = stitch DwarfPlanet chooseDwarfPlanets 
          astroids = stitch Astroid chooseAstroids
          comets = stitch Comet chooseComets
          gasClouds = stitch GasCloud chooseGasClouds
          emptys (os, is) = os ++ fmap (, EmptySpace) is
          indexSolutions = fmap emptys . concatMap gasClouds . concatMap comets . concatMap astroids . dwarfs $ ([], [1..18])