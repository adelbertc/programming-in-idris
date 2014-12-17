module playground
%language TypeProviders

data Parity : Nat -> Type where
  Even : Parity (n + n)
  Odd : Parity (S (n + n))

parity : (n : Nat) -> Parity n

natToBin : Nat -> List Bool
natToBin Z = []
natToBin k with (parity k)
  natToBin (j + j) | Even = False :: natToBin j
  natToBin (S (j + j)) | Odd = True :: natToBin j

putStr' : String -> IO ()
putStr' x = mkForeign (FFun "putStr" [FString] FUnit) x

strToType : String -> Type
strToType "Int" = Int
strToType _ = Nat

fromFile : String -> IO (Provider Type)
fromFile fname = do str <- readFile fname
                    return (Provide (strToType (trim str)))

%provide (T1 : Type) with fromFile "theType"

foo : T1
foo = 2
