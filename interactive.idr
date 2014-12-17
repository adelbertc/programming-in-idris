module interactive

vzipWith : (a -> b -> c) -> Vect n a -> Vect n b -> Vect n c
vzipWith f [] [] = []
vzipWith f (x :: xs) (y :: ys) = f x y :: vzipWith f xs ys
