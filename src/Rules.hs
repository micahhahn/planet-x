module Rules where

import Data.Word (Word64)
import Data.Vector (Vector)
import qualified Data.Vector as V 
import Data.Bits

import PlanetX

newtype Solution = Solution { unSolution :: Word64 }
    deriving (Show)

objects = fmap (uncurry replicate) [(2, Comet), (4, Astroid), (4, DwarfPlanet), (2, GasCloud), (6, EmptySpace)]

packSolution :: Vector Object -> Solution
packSolution = Solution . foldr (\o w -> shiftL w 3 .|. fromIntegral (fromEnum o)) 0

unpackSolution :: Solution -> Vector Object
unpackSolution (Solution w) = V.fromList $ fmap (\i -> toEnum . fromIntegral $ shiftR w (3 * i) .&. 7) [0..17]

combo :: [[a]] -> [[a]]
combo (a:as) = f [] a as
    where f :: [[a]] -> [a] -> [[a]] -> [[a]]
          f ls [] (r:rs) = f ls r rs
          f ls (c:cs) (r:rs) = fmap (c:) (f (cs:ls) r rs) ++ f ((c:cs):ls) r rs
