module sintax

boolCase : (x : Bool) -> Lazy a -> Lazy a -> a
boolCase True t e = t
boolCase False t e = e

syntax "if" [test] "then" [t] "else" [e] = boolCase test t e

-- data Interval : Type where
--   MkInterval : (lower : Float) -> (upper : Float) -> so (lower < upper) -> Interva;
-- 
-- pattern syntax "[" [x] "..." [y] "]" = MkInterval x y oh
-- term    syntax "[" [x] "..." [y] "]" = MkInterval x y ?bounds_lemma

-- syntax "for" {x} "in" [xs] ":" [body] = forLoop xs (\x => body)
-- 
-- main : IO ()
-- main = do for x in [1..10]:
--               putStrLn ("Number " ++ show x)
--         putStrLn "Done!"

-- isCons : List a -> Bool
-- isCons [] = False
-- isCons (x :: xs) = True

head : (xs : List a) -> { auto p : isCons xs = True } -> a
head (x :: xs) = x

head' : (xs : List a) -> { default proof { trivial } p : isCons xs = True } -> a
head' (x :: xs) = x

implicit intString : Int -> String
intString = show

test : Int -> String
test x = "Number " ++ x
