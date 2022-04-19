
import Test.QuickCheck

addPoly :: [Int] -> [Int] -> [Int]
addPoly [] ys = ys
addPoly xs [] = xs
addPoly (x:xs) (y:ys) = x + y : addPoly xs ys 



subPoly :: [Int] -> [Int] -> [Int]
subPoly xs ys = addPoly xs (negPoly ys)

negPoly :: [Int] -> [Int]
negPoly [] = []
negPoly (x:xs) = (-x) : negPoly xs  

-- shift_right 2 [1,2] will produce [0,0,1,2]
shift_right :: Int -> [Int] -> [Int]
shift_right n xs = (replicate n 0) ++ xs

shiftRight' :: Int -> [Int] -> [Int]
shiftRight' 0 xs = xs
shiftRight' n xs = 0 :: shiftRight (n-1) xs

mulPoly :: [Int] -> [Int] -> [Int]
mulPoly [] ys = []
mulPoly xs [] = []
mulPoly (x:xs) ys = addPoly (map (x*) ys) (0:mulPoly xs ys)


-----------------------------------------
------------------- Karatsuba

karatsuba :: [Int] -> [Int] -> [Int]
karatsuba [] xs = []
karatsuba ys [] = []
karatsuba [x] ys = map (x*) ys 
karatsuba xs [y] = map (y*) xs 
karatsuba [x1,x2] ys = mulPoly [x1,x2] ys
karatsuba xs [y1,y2] = mulPoly xs [y1,y2]
karatsuba xs ys  =   let m = min (div (length xs) 2) (div (length ys) 2) in
                      let (b,a) = splitAt m xs in
                      let (d,c) = splitAt m ys in 
                      let ac = karatsuba a c in 
                      let bd = karatsuba b d in
                      let a_plus_b = addPoly a b in 
                      let c_plus_d = addPoly c d in
                      let ad_plus_bc = ((karatsuba a_plus_b c_plus_d) `subPoly` ac) `subPoly` bd   in
                      ((shift_right (2*m) ac) `addPoly` (shift_right m ad_plus_bc)) `addPoly`  bd


-----------------------------------------
------------------- Test

dropZeroes :: [Int] -> [Int]
dropZeroes xs = reverse $ dropWhile (==0) $ reverse xs

prop :: [Int] -> [Int] -> Bool
prop a b =   (karatsuba a b) == (mulPoly a b)
