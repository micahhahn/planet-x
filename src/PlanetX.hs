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
          deriving (Eq, Ord)

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

-- There are 4 astroids, and they come in pairs.  i.e. each astroid must be next to at least one other astroid
astroidE :: State Int (Exp VarX)
astroidE = do
    let astroids = Var . VarX Astroid <$> [1..sectorCount]
    exactly4 <- kEQ astroids 4

    -- e.g. (D1 => D18 | D2) & (D2 => D1 | D3) & ...
    let astroidAdj = allOf [ a `Imp` (prev' a `Or` next' a) | a <- astroids]

    return $ allOf [exactly4, astroidAdj]

-- There are 4 dwarf planets and they must be in a band of exactly 6, this leads to 6 possible configurations:
-- DDDxxD | DDxDxD | DxDDxD | DDxxDD | DxDxDD | DxxDDD
dwarfPlanetE :: State Int (Exp VarX)
dwarfPlanetE = do
    let dwarfPlanets = fmap mkDwarf [1..sectorCount]
    exactly4 <- kEQ dwarfPlanets 4

    -- e.g. (D1 => !D7 & !D8 & !D9 & !D10 & !D11 & !D12 & !D13)
    let bandOf6 = allOf [p `Imp` allOf [Not q | q <- dwarfPlanets, distance' p q > 5] | p <- dwarfPlanets]

    -- Enforce exactness of band of 6 boundary condition by verifing that there exists a pair of dwarf planets 6 sectors apart
    -- e.g. (D1 & D6) | (D2 & D7) | ...
    -- We need to use auxiliary variables to represent this efficiently in cnf
    -- e.g. (v1 <=> D1 & D6) | (v2 <=> D2 & D7) | ... | (v1 | v2 | ...)
    boundaryVars <- mapM (\i -> freshVar >>= (\v -> return (v, v `Equiv` mkBoundary i))) [1..sectorCount]
    let boundaryBindings = allOf (fmap snd boundaryVars)
    let boundary = anyOf (fmap fst boundaryVars)

    return $ allOf [exactly4, bandOf6, boundaryBindings, boundary]

    where mkDwarf = Var . VarX DwarfPlanet
          mkBoundary i = mkDwarf i `And` mkDwarf ((i + 4) `mod` sectorCount + 1)

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
    let nots = allOf $ mkComet <$> [1, 4, 6, 8, 9, 10, 12, 14, 15, 16, 18]
    pairs <- kEQ (mkComet <$> [2, 3, 5, 7, 11, 13, 17]) 2
    return $ allOf [nots, pairs]

    where mkComet = Var . VarX Comet

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

next :: Int -> Int
next i = i `mod` sectorCount + 1

next' :: Exp VarX -> Exp VarX
next' (Var (VarX o i)) = Var . VarX o $ i `mod` sectorCount + 1

prev :: Int -> Int
prev i = (i - 2) `mod` sectorCount + 1

prev' :: Exp VarX -> Exp VarX
prev' (Var (VarX o i)) = Var . VarX o $ (i - 2) `mod` sectorCount + 1

distance :: VarX -> VarX -> Int
distance (VarX _ s1) (VarX _ s2) = let min' = min s1 s2
                                       max' = max s1 s2
                                    in min (max' - min') (min' + sectorCount - max')

distance' :: Exp VarX -> Exp VarX -> Int
distance' (Var l) (Var r) = distance l r

adjacent :: VarX -> VarX -> Bool
adjacent s1 s2 = distance s1 s2 == 1

opposite :: VarX -> VarX -> Bool
opposite s1 s2 = distance s1 s2 == sectorCount `div` 2