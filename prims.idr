module prims

x : Int
x = 42

foo : String
foo = "Sausage machine"

bar : Char
bar = 'Z'

quux : Bool
quux = False

data Elem : a -> Vect n a -> Type where
  Here : {x : a} -> {xs : Vect n a} -> Elem x (x :: xs)
  There : {x, y : a} -> {xs : Vect n a} -> Elem x xs -> Elem x (y :: xs)

testVec : Vect 4 Int
testVec = 3 :: 4 :: 5 :: 6 :: Nil

inVect : Elem 5 testVec
inVect = There (There Here)

using (x:a, y:a, xs:Vect n a)
  data Elem' : a -> Vect n a -> Type where
    Here' : Elem' x (x :: xs)
    There' : Elem' x xs -> Elem' x (y :: xs)

mutual
  even : Nat -> Bool
  even Z = True
  even (S k) = odd k

  odd : Nat -> Bool
  odd Z = False
  odd (S k) = even k

boolCase : Bool -> Lazy a -> Lazy a -> a
boolCase True t e = t
boolCase False t e = e

intVec : Vect 5 Int
intVec = [1, 2, 3, 4, 5]

double : Int -> Int
double x = x * 2

list_lookup : Nat -> List a -> Maybe a
list_lookup _ Nil = Nothing
list_lookup Z (x :: xs) = Just x
list_lookup (S k) (x :: xs) = list_lookup k xs

vec : (n : Nat ** Vect n Int)
vec = (2 ** [3, 4])

vec' : Sigma Nat (\n => Vect n Int)
vec' = MkSigma 2 [3, 4]

inBounds : Int -> Int -> Bool
inBounds x y = x >= 0 && x < 640 && y >= 0 && y < 480

mirror : List a -> List a
mirror xs = let xs' = reverse xs in
                xs ++ xs'

data Person = MkPerson String Int

showPerson : Person -> String
showPerson p = let MkPerson name age = p in
                   name ++ " is " ++ show age ++ " years old"

pythag : Int -> List (Int, Int, Int)
pythag n = [ (x, y, z) | z <- [1..n], y <- [1..z], x <- [1..y], x * x + y * y == z * z ]

splitAt : Char -> String -> (String, String)
splitAt c x = case break (== c) x of
                   (x, y) => (x, strTail y)

lookup_default : Nat -> List a -> a -> a
lookup_default i xs def = case list_lookup i xs of
                               Nothing => def
                               Just x => x

record Person : Type where
  MkPerson' : (name : String) -> (age : Int) -> Person

fred : Person
fred = MkPerson' "Fred" 30

record Class : Type where
  ClassInfo : (students : Vect n Person) -> (className : String) -> Class

addStudent : Person -> Class -> Class
addStudent p c = record { students = p :: students c } c

sort' : Ord a => List a -> List a
sort' [] = []
sort' (x :: []) = x :: []
sort' (x :: xs) = let (l, r) = partition (< x) xs in (sort' l) ++ [x] ++ (sort' r)

-- sort'' : Ord a => Vect n a -> Vect n a
-- sort'' [] = []
-- sort'' (x :: []) = x :: []
-- sort'' (x :: xs) = let (l, r) = partition (< x) xs in (sort'' l) ++ [x] ++ (sort'' r)

m_add : Maybe Int -> Maybe Int -> Maybe Int
m_add x y = do x' <- x
               y' <- y
               return (x' + y')

m_add' : Maybe Int -> Maybe Int -> Maybe Int
m_add' x y = return (!x + !y)

m_add'' : Maybe Int -> Maybe Int -> Maybe Int
m_add'' x y = [ x' + y' | x' <- x, y' <- y ]

m_app : Maybe (a -> b) -> Maybe a -> Maybe b
m_app (Just f) (Just a) = Just (f a)
m_app _ _ = Nothing

m_add''' : Maybe Int -> Maybe Int -> Maybe Int
m_add''' x y = m_app (m_app (Just (+)) x) y

m_add'''' : Maybe Int -> Maybe Int -> Maybe Int
m_add'''' x y = [| x + y |]

data Expr = Var String
          | Val Int
          | Add Expr Expr

data Eval : Type -> Type where
  MkEval : (List (String, Int) -> Maybe a) -> Eval a

fetch : String -> Eval Int
fetch x = MkEval fetchVal where
  fetchVal : List (String, Int) -> Maybe Int
  fetchVal [] = Nothing
  fetchVal ((v, val) :: xs) = if (x == v) then (Just val) else (fetchVal xs)

instance Functor Eval where
  map f (MkEval g) = MkEval (\e => map f (g e))

instance Applicative Eval where
  pure x = MkEval (\e => Just x)

  (<$>) (MkEval f) (MkEval g) = MkEval (\x => app (f x) (g x)) where
    app : Maybe (a -> b) -> Maybe a -> Maybe b
    app (Just fx) (Just gx) = Just (fx gx)
    app _ _ = Nothing

eval : Expr -> Eval Int
eval (Var x) = fetch x
eval (Val x) = [| x |]
eval (Add x y) = [| eval x + eval y |]

runEval : List (String, Int) -> Expr -> Maybe Int
runEval env e = case eval e of
  MkEval envFn => envFn env

instance [myord] Ord Nat where
  compare Z (S n) = GT
  compare (S n) Z = LT
  compare Z Z = EQ
  compare (S x) (S y) = compare @{myord} x y

testList : List Nat
testList = [3,4,1]
