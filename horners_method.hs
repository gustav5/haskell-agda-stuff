module horners_method where
import Data.digits

    
horners :: Int -> [Int] -> Int
horners _ [] = 0
horners x (a:as) = a + x*(horners x as)
