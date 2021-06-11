module Query where

import PlanetX

data Query = Survey Int Int Object
           | Target Int
           deriving (Show)

queryCost :: Query -> Int
queryCost (Survey _ l _) 
    | l <= 3 = 4
    | l <= 6 = 3
    | l <= 9 = 2
    | otherwise = error "Invalid Survey length"
queryCost (Target _) = 4

