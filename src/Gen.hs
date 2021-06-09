{-# LANGUAGE TupleSections #-}

module Gen (
    solutions,
    Solution(..)
) where 

import PlanetX
import Logic
import Data.List ((\\), sortBy, zip5, intercalate, intersperse)

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

choosePlanetX :: SolutionBuilder -> [[Int]]
choosePlanetX (os, is) = (:[]) <$> filter (\i -> not $ any (\(oi, o) -> (nextSector oi == i || nextSector i == oi) && o == DwarfPlanet) os) is

chooseGasClouds :: [Int] -> [[Int]]
chooseGasClouds is = gasClouds
    where triples = zip3 (drop (length is - 1) . cycle $ is) is (drop 1 . cycle $ is)
          triples' = [v | v@(l, c, r) <- triples, nextSector l == c || nextSector c == r]
          gasClouds = [ [c1, c2] | [(l1, c1, _), (_, c2, r2)] <- choose triples' 2, nextSector c1 /= c2 || (nextSector l1 == c1 && nextSector c2 == r2) ]

stitch :: Object -> ([Int] -> [[Int]]) -> SolutionBuilder -> [SolutionBuilder]
stitch o f (objs, is) = fmap (\ds -> (objs ++ fmap (, o) ds, is \\ ds) ) (f is)

newtype Solution = Solution { unSolution :: [Object] }

instance Show Solution where
    show (Solution x) = f x
        where f [] = ""
              f (o:os) = g o : f os
              g o = case o of
                        Astroid -> 'A'
                        Comet -> 'C'
                        DwarfPlanet -> 'D'
                        EmptySpace -> 'E'
                        GasCloud -> 'G'
                        PlanetX -> 'X'

solutions :: [Solution]
solutions = filter validXLocations s'
    where dwarfs = stitch DwarfPlanet chooseDwarfPlanets 
          astroids = stitch Astroid chooseAstroids
          comets = stitch Comet chooseComets
          gasClouds = stitch GasCloud chooseGasClouds
          emptys (os, is) = os ++ fmap (, EmptySpace) is
          indexSolutions = fmap emptys . concatMap gasClouds . concatMap comets . concatMap astroids . dwarfs $ ([], [1..18])
          s' = Solution . fmap snd . sortBy (\i1 i2 -> compare (fst i1) (fst i2)) <$> indexSolutions

solutionsX :: [Solution]
solutionsX = Solution . fmap snd . sortBy (\i1 i2 -> compare (fst i1) (fst i2)) <$> indexSolutions
    where dwarfs = stitch DwarfPlanet chooseDwarfPlanets 
          astroids = stitch Astroid chooseAstroids
          comets = stitch Comet chooseComets
          planetX s@(objs, is) = fmap (\ds -> (objs ++ fmap (, PlanetX) ds, is \\ ds) ) (choosePlanetX s)
          gasClouds = stitch GasCloud chooseGasClouds
          emptys (os, is) = os ++ fmap (, EmptySpace) is
          indexSolutions = fmap emptys . concatMap gasClouds . concatMap planetX .  concatMap comets . concatMap astroids . dwarfs $ ([], [1..18])

writeSolutions :: IO ()
writeSolutions = do
    let x = intercalate "\n" $ fmap (intersperse '\t' . show) solutionsX
    writeFile "C:/Users/Micah/Desktop/solutions.txt" x

-- validXLocations :: [Object] -> Int
validXLocations :: Solution -> Bool
validXLocations (Solution os) = not (null valid)
    where zipped = zip5 (drop 16 . cycle $ os) (drop 17 . cycle $ os) os (drop 1 . cycle $ os) (drop 2 . cycle $ os)
          valid = [ () | (l2, l1, c, r1, r2) <- zipped, c == EmptySpace && l1 /= DwarfPlanet && r1 /= DwarfPlanet && (l1 /= GasCloud || l2 == EmptySpace) && (r1 /= GasCloud || r2 == EmptySpace)]