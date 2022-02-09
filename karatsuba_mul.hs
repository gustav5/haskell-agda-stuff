import Test.QuickCheck

int_to_tup :: Int -> (String,String)
int_to_tup x = let y = show x in (take (div (length y) 2) y, drop (div (length y) 2) y)

str_tup_to_int :: (String,String) -> (Int,Int)
str_tup_to_int (x,y) = (read x :: Int, read y :: Int)

split_num :: Int -> (Int,Int)
split_num x = str_tup_to_int (int_to_tup x) 

karatsuba :: Integer -> Integer -> Integer
karatsuba x y | x < 10 || y < 10 = x*y 
              | otherwise =  let (r,s) = ((split_num x),(split_num y)) in karatsuba' (fst r) (snd r) (fst s) (snd s) (div ((toInteger . length . show) y) 2)

karatsuba' :: Integer -> Integer -> Integer -> Integer -> Integer -> Integer
karatsuba' a b c d half = let (ac,bd) = (karatsuba a c, karatsuba b d) in (10^(2*half))*ac + (10^half)*((karatsuba (a+b) (c+d)) - ac - bd ) + bd

prop a b = (karatsuba a b) == a*b 
