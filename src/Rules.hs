module Rules where

import Data.Word (Word64)
import Data.Vector (Vector)
import qualified Data.Vector as V 
import Data.Bits

import PlanetX

newtype Solution = Solution { unSolution :: Word64 }
    deriving (Show)

c = V.fromList [ Astroid, Astroid, Astroid, Astroid, Comet, Comet, DwarfPlanet, DwarfPlanet, DwarfPlanet, DwarfPlanet, EmptySpace, EmptySpace, EmptySpace, EmptySpace, EmptySpace, GasCloud, GasCloud, PlanetX ]

packSolution :: Vector Object -> Solution
packSolution = Solution . foldr (\o w -> shiftL w 3 .|. fromIntegral (fromEnum o)) 0

unpackSolution :: Solution -> Vector Object
unpackSolution (Solution w) = V.fromList $ fmap (\i -> toEnum . fromIntegral $ shiftR w (3 * i) .&. 7) [0..17]