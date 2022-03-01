
import Test.QuickCheck
import Data.Char (digitToInt)




karatsuba :: [Int] -> [Int] -> [Int]
karatsuba xs ys | xs == [] = []
                | ys == [] = []
                | otherwise = karatsuba2 xs ys

karatsuba2 :: [Int] -> [Int] -> [Int]
karatsuba2 xs ys    | length xs < 2 || length ys < 2 = mulPoly xs ys
                    | otherwise =
                        let m = min (div (length xs) 2) (div (length ys) 2) in
                        let (b,a) = splitAt m xs in
                        let (d,c) = splitAt m ys in 
                        let ac = karatsuba2 a c in 
                        let bd = karatsuba2 b d in
                        let ad_plus_bc = subPoly (subPoly (karatsuba2 (addPoly a b) (addPoly c d)) ac) bd in
                        addPoly (addPoly (shift_right (2*m) ac) (shift_right m ad_plus_bc)) bd



addPoly :: [Int] -> [Int] -> [Int]
addPoly xs ys = if length xs < length ys
  then zipWith (+) xs ys ++ drop (length xs) ys
  else zipWith (+) xs ys ++ drop (length ys) xs
-- zipWith :: (a -> b -> c) -> [a] -> [b] -> [c]

subPoly :: [Int] -> [Int] -> [Int]
subPoly xs ys = if length xs < length ys
  then zipWith (-) xs ys ++ drop (length xs) ys
  else zipWith (-) xs ys ++ drop (length ys) xs


-- shift_right 2 [1,2] will produce [0,0,1,2]
shift_right :: Int -> [Int] -> [Int]
shift_right n xs = (replicate n 0) ++ xs

mulPoly :: [Int] -> [Int] -> [Int]
mulPoly [] ys = []
mulPoly xs [] = []
mulPoly (x:xs) ys = addPoly (map (x*) ys) (0:mulPoly xs ys)
-- map :: (a -> b) -> [a] -> [b]
-- foldr :: (a -> b -> b) -> b -> [a] -> b

dropZeroes :: [Int] -> [Int]
dropZeroes xs = reverse $ dropWhile (==0) $ reverse xs

int_to_li :: Int -> [Int]
int_to_li xs = map digitToInt (show xs)

prop :: [Int] -> [Int] -> Bool
prop a b =  (dropZeroes (karatsuba a b)) == (dropZeroes (mulPoly a b))