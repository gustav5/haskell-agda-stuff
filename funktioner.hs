



zipWith' :: (a -> b -> c) -> [a] -> [b] -> [c]
zipWith' f [] _ = []
zipWith' f _ [] = []
zipWith' f (x:xs) (y:ys) = f x y : zipWith' f xs ys


take'  :: Int -> [a] -> [a]
take' n _      | n <= 0 =  []
take' _ []              =  []
take' n (x:xs)          =  x : take' (n-1) xs


drop' :: Int -> [a] -> [a]
drop' n xs      | n <= 0 = xs
drop' _ []      = []
drop' n (_:xs)  = drop' (n-1) xs

replicate' :: Int -> a -> [a]
replicate' 0 _ = []
replicate' n x =  x : replicate' (n-1) x

shift_right :: Int -> [Int] -> [Int]
shift_right n xs = (replicate n 0) ++ xs

splitAt' :: Int -> [a] -> ([a],[a])
splitAt' n xs = (take' n xs, drop n xs)