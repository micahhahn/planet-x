module PlanetX where

import Control.Monad.State.Lazy

import Encode
import Exp
import Logic

data Object = Astroid
            | Comet
            | DwarfPlanet
            | EmptySpace
            | GasCloud
            | PlanetX
            deriving (Eq, Show, Ord, Enum, Bounded) 

data VarX = VarX Object Int
          | Aux Int

instance Show VarX where
    show (VarX o i) = (case o of
        Astroid -> "A"
        Comet -> "C"
        DwarfPlanet -> "D"
        EmptySpace -> "E"
        GasCloud -> "G"
        PlanetX -> "X") ++ show i

    show (Aux i) = "v" ++ show i

instance Encode VarX where
    encode (VarX o s) = (s - 1) * objectCount + (fromEnum o + 1)
    encode (Aux i) = i + (objectCount * sectorCount)

    decode i = if i > (objectCount * sectorCount)
               then Aux $ i - (objectCount * sectorCount)
               else VarX (toEnum $ (i - 1) `mod` objectCount) (((i - 1) `div` objectCount) + 1)

    rank _ = objectCount * sectorCount

objectCount = length ([minBound..maxBound] :: [Object])
sectorCount = 18

sectorUniqueE = fmap (foldl1 And) . sequence $ (\s -> binaryEO $ (Var . flip VarX s) <$> ([minBound..maxBound] :: [Object])) <$> [1..sectorCount]

sectorUniqueE2 :: State Int (Exp VarX)
sectorUniqueE2 = fmap (foldl1 And) . sequence $ (\s -> kEQ ((Var . flip VarX s) <$> ([minBound..maxBound] :: [Object])) 1) <$> [1..sectorCount]

astroidE :: State Int (Exp VarX)
astroidE = binaryEO exps
    where astroids = VarX Astroid <$> [1..sectorCount]
          combos = choose astroids 4
          refine = filter (\ss -> all (\s -> any (adjacent s) ss) ss) combos
          exps = flip excludeOtherSectors Astroid <$> refine

astroidE2 :: State Int (Exp VarX)
astroidE2 = do
    let astroids = Var . VarX Astroid <$> [1..sectorCount]
    exactly4 <- kEQ astroids 4
    let astroidAdj = foldl1 And $ (\i -> (Var $ VarX Astroid i) `Imp` ((Var . VarX Astroid . prev $ i) `Or` (Var . VarX Astroid . next $ i))) <$> [1..sectorCount]
    return $ exactly4 `And` astroidAdj

dwarfPlanetE = binaryEO exps
    where dwarfPlanets = VarX DwarfPlanet <$> [1..sectorCount]
          combos = choose dwarfPlanets 4
          refine = filter (\ss -> all (\(l:r:[]) -> distance l r < 6) (choose ss 2)) combos
          exps = flip excludeOtherSectors DwarfPlanet <$> refine

dwarfPlanetE2 :: State Int (Exp VarX)
dwarfPlanetE2 = do
    let dwarfPlanets = VarX DwarfPlanet <$> [1..sectorCount]
    exactly4 <- kEQ (Var <$> dwarfPlanets) 4
    let bandOf6 = foldl1 And $ (\d1 -> Imp (Var d1) $ foldl1 And . concat $ (\d2 -> if distance d1 d2 > 5 then [Not $ Var d2] else []) <$> dwarfPlanets) <$> dwarfPlanets
    return $ exactly4 `And` bandOf6

excludeOtherSectors :: [VarX] -> Object -> Exp VarX
excludeOtherSectors vs o = foldl1 And $ merge vs [1..sectorCount]

    where merge v@((VarX o' i):vs') (s:ss') = if i == s then (Var $ VarX o' i) : merge vs' ss' else (Not . Var $ VarX o s) : merge v ss' 
          merge _ (s:ss') = (Not . Var $ VarX o s) : merge [] ss' 
          merge _ _ = []

-- Not all the other locatoins! 
cometE :: State Int (Exp VarX)
cometE = do
    let nots = foldl1 And $ Not . Var . VarX Comet <$> [1, 4, 6, 8, 9, 10, 12, 14, 15, 16, 18]
    pairs <- binaryEO exprs
    return $ nots `And` pairs
    
    where comets = VarX Comet <$> [2, 3, 5, 7, 11, 13, 17]
          exprs = foldl1 And . fmap Var <$> choose comets 2

cometE2 :: State Int (Exp VarX)
cometE2 = do
    let nots = foldl1 And $ Not . Var . VarX Comet <$> [1, 4, 6, 8, 9, 10, 12, 14, 15, 16, 18]
    pairs <- kEQ (Var . VarX Comet <$> [2, 3, 5, 7, 11, 13, 17]) 2
    return $ nots `And` pairs

planetXE :: State Int (Exp VarX)
planetXE = do
    exactlyOne <- binaryEO $ Var . VarX PlanetX <$> [1..sectorCount]
    let notNextToDwarf = foldl1 And $ mkCon <$> [1..sectorCount]
    return $ exactlyOne `And` notNextToDwarf
    
    where mkCon i = Var (VarX PlanetX i) `Imp` ((Not . Var . VarX DwarfPlanet $ prev i) `And` (Not . Var . VarX DwarfPlanet $ next i)) 

planetXE2 :: State Int (Exp VarX)
planetXE2 = do
    exactlyOne <- kEQ (Var . VarX PlanetX <$> [1..sectorCount]) 1
    let notNextToDwarf = foldl1 And $ mkCon <$> [1..sectorCount]
    return $ exactlyOne `And` notNextToDwarf
    
    where mkCon i = Var (VarX PlanetX i) `Imp` ((Not . Var . VarX DwarfPlanet $ prev i) `And` (Not . Var . VarX DwarfPlanet $ next i)) 

gasCloudE :: State Int (Exp VarX)
gasCloudE = do
    let emptyAjacent = foldl1 And $ (\s -> (Var $ VarX GasCloud s) `Imp` ((Var $ VarX EmptySpace (prev s)) `Or` (Var $ VarX EmptySpace (next s)))) <$> [1..sectorCount]
    exactlyTwo <- binaryEO $ foldl1 And <$> choose (Var . VarX GasCloud <$> [1..sectorCount]) 2
    return $ emptyAjacent `And` exactlyTwo

gasCloudE2 :: State Int (Exp VarX)
gasCloudE2 = do
    let emptyAjacent = foldl1 And $ (\s -> (Var $ VarX GasCloud s) `Imp` ((Var $ VarX EmptySpace (prev s)) `Or` (Var $ VarX EmptySpace (next s)))) <$> [1..sectorCount]
    exactlyTwo <- kEQ (Var . VarX GasCloud <$> [1..sectorCount]) 2
    return $ emptyAjacent `And` exactlyTwo

takeUntil :: (a -> Bool) -> [a] -> [a]
takeUntil _ [] = []
takeUntil p (a:as) = a : (if p a then [] else takeUntil p as) 

survey :: Object -> (Int, Int) -> Int -> State Int (Exp VarX)
survey o (l, r) = kEQ sectors
    where sectors = case o of 
                    EmptySpace -> (Var . VarX o <$> sectors') ++ (Var . VarX PlanetX <$> sectors')
                    _ -> Var . VarX o <$> sectors'
          sectors' = takeUntil (== r) $ (\i -> (l + i - 1) `mod` sectorCount + 1) <$> [0..]

s = sorted (Var . VarX Astroid <$> sectors')
    where sectors' = takeUntil (== 3) $ (\i -> (17 + i - 1) `mod` sectorCount + 1) <$> [0..]

next :: Int -> Int
next i = i `mod` sectorCount + 1

prev :: Int -> Int
prev i = (i - 2) `mod` sectorCount + 1

distance :: VarX -> VarX -> Int
distance (VarX _ s1) (VarX _ s2) = let min' = min s1 s2
                                       max' = max s1 s2
                                    in min (max' - min') (min' + sectorCount - max')

adjacent :: VarX -> VarX -> Bool
adjacent s1 s2 = distance s1 s2 == 1

opposite :: VarX -> VarX -> Bool
opposite s1 s2 = distance s1 s2 == sectorCount `div` 2