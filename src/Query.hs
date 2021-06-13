module Query where

import Data.Map (Map)
import qualified Data.Map as Map

import Gen
import PlanetX

data Query = Survey Int Int Object
           | Target Int
           deriving (Show)

data QueryResult = SurveyResult Int
                 | TargetResult Object
                 deriving (Show, Eq, Ord)

queryCost :: Query -> Int
queryCost (Survey _ l _) 
    | l <= 3 = 4
    | l <= 6 = 3
    | l <= 9 = 2
    | otherwise = error "Invalid Survey length"
queryCost (Target _) = 4

query :: Query -> Solution -> QueryResult
query (Target i) (Solution os) = case os !! i of
    PlanetX -> TargetResult EmptySpace 
    o -> TargetResult o 
query (Survey i l o) (Solution os) = SurveyResult . sum . fmap (f o) . take l . drop i . cycle $ os
    where f :: Object -> Object -> Int
          f (EmptySpace) (PlanetX) = 1
          f o1 o2 = fromEnum (o1 == o2)

thunk :: Query -> [PartialSolution] -> Map QueryResult [PartialSolution]
thunk q ss = Map.fromListWith (++) $ fmap (\(PartialSolution (s, i)) -> (query q s, [PartialSolution (s, i)])) ss