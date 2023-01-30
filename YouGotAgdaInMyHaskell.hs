module YouGotAgdaInMyHaskell where

map :: (a -> b) -> [a] -> [b]
map f [] = []
map f (x : xs) = f x : map f xs

min :: Ord a => a -> a -> a
min x y = if x < y then x else y

data Vec a = Nil
           | Cons a (Vec a)

interleave :: Vec a -> Vec a -> Vec a
interleave Nil ys = ys
interleave (Cons x xs) ys = Cons x (interleave ys xs)

