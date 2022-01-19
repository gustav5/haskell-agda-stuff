

int_to_tup :: Int -> (String,String)
int_to_tup x = let y = show x in (take (div (length y) 2) y, drop (div (length y) 2) y)

str_tup_to_int :: (String,String) -> (Int,Int)
str_tup_to_int (x,y) = (read x :: Int, read y :: Int)

split_num :: Int -> (Int,Int)
split_num x = str_tup_to_int (int_to_tup x) 



karatsuba :: Int -> Int -> Int
karatsuba x y | ((length  (show x)) < 10) || ((length (show y)) < 10) = x*y
              | otherwise =  let (r,s) = ((split_num x),(split_num y)) in karatsuba' (fst r) (snd r) (fst s) (snd s) (max (length r) (length s))

karatsuba' :: Int -> Int -> Int -> Int -> Int -> Int
karatsuba' a b c d n = let (ac,bd) = (karatsuba a c, karatsuba b d) in (10^n)*ac + ((10^(div n 2))*(karatsuba (a+b) (c+d)) - ac - bd )+ bd
