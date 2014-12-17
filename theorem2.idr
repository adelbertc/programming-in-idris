module theorem2

data Parity : Nat -> Type where
  Even : Parity (n + n)
  Odd : Parity (S (n + n))

parity : (n : Nat) -> Parity n
parity Z = Even {n = Z}
parity (S Z) = Odd {n = Z}
parity (S (S k)) with (parity k)
  parity (S (S (j + j))) | Even ?= Even {n = S j}
  parity (S (S (S (j + j)))) | Odd ?= Odd {n = S j}

data Binary : Nat -> Type where
  bEnd : Binary Z
  bO : Binary n -> Binary (n + n)
  bI : Binary n -> Binary (S (n + n))

natToBin : (n : Nat) -> Binary n
natToBin Z = bEnd
natToBin (S k) with (parity k)
    natToBin (S (j + j)) | even = bI (natToBin j)
    natToBin (S (S (j + j))) | odd ?= bO (natToBin (S j))
