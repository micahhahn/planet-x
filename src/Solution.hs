module Solution where

import Data.Bits
import Data.Word

import PlanetX

-- We're going to hold something like 1,000,000 solutions in memory at once, so a compact representation is important
-- The lowest 54 bits are grouped into triplets represeting the object in the 18 sectors.  The value is the enum representation
-- of Object (without PlanetX).  This allows for quick sequential enumeration of Objects.
--
-- The next 6 bits are boolean fields depicting if planetx could take the place of the relevant EmptySpace.  There should always
-- be at least one of these bits set. This allows for quick counting of potential positions of X (useful for probabilities).
-- 
--   0000 000000 000 000 000 000 000 000 000 000 000 000 000 000 000 000 000 000 000 000
--        |    | s18 s17 s16 s15 s14 s13 s12 s11 s10 s9  s8  s7  s6  s5  s4  s3  s2  s1
--        |    |
-- |  0  0  0  0  0  0 |
--   X6 X5 X4 X3 X2 X1

newtype Solution = Solution { unSolution :: Word64 }

countX :: Solution -> Int
countX (Solution w) = popCount (w .&. 0x0FA0000000000000)

unpackObjects :: Solution -> [Object]
unpackObjects (Solution w) = fmap f [0..17]
    where f i = toEnum . fromIntegral $ shift w  (i * (-3)) .&. 0x0000000000000003