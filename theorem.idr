module theorem

fiveIsFive : 5 = 5
fiveIsFive = Refl

twoPlusTwo : 2 + 2 = 4
twoPlusTwo = Refl

disjoint : (n : Nat) -> Z = S n -> Void
disjoint n p = replace {P = disjointTy} p ()
  where
    disjointTy : Nat -> Type
    disjointTy Z = ()
    disjointTy (S k) = Void

plusReduces : (n : Nat) -> plus Z n = n
plusReduces n = Refl

plusReducesZ : (n : Nat) -> n = plus n Z
plusReducesZ Z = Refl
plusReducesZ (S k) = cong (plusReducesZ k)

plusReducesS : (n : Nat) -> (m : Nat) -> S (plus n m) = plus n (S m)
plusReducesS Z m = Refl
plusReducesS (S k) m = cong (plusReducesS k m)

plusReducesZ' : (n : Nat) -> n = plus n Z
plusReducesZ' Z = ?plusred_Z_Z
plusReducesZ' (S k) = let ih = plusReducesZ' k in ?plusred_Z_S

empty1 : Void
empty1 = hd [] where
  hd : List a -> a
  hd (x :: xs) = x

empty2 : Void
empty2 = empty2

total
qsort : Ord a => List a -> List a
qsort [] = []
qsort (x :: xs) = qsort (assert_smaller (x :: xs) (filter (< x) xs)) ++
                    (x :: qsort (assert_smaller (x :: xs) (filter (>= x) xs)))

data Parity : Nat -> Type where
  Even : Parity (n + n)
  Odd : Parity (S (n + n))

parity : (n : Nat) -> Parity n
parity Z = Even {n = Z}
parity (S Z) = Odd {n = Z}
parity (S (S k)) with (parity k)
  parity (S (S (j + j))) | Even ?= Even {n = S j}
  parity (S (S (S (j + j)))) | Odd ?= Odd {n = S j}

parity' : (n : Nat) -> Parity n
parity' Z = Even {n = Z}
parity' (S k) with (parity k)
  parity' (S (plus n n)) | Even = ?parity_rhs_1
  parity' (S (S (plus n n))) | Odd = ?parity_rhs_2

data Binary : Nat -> Type where
  bEnd : Binary Z
  bO : Binary n -> Binary (n + n)
  bI : Binary n -> Binary (S (n + n))

-- natToBin : (n : Nat) -> Binary n
-- natToBin Z = bEnd
-- natToBin (S k) with (parity k)
--   natToBin (S (j + j)) | even = bI (natToBin j)
--   natToBin (S (S (j + j))) | odd ?= bO (natToBin (S j))

---------- Proofs ----------

theorem.parity_lemma_1 = proof
  intro
  intro
  exact believe_me value

theorem.parity_lemma_2 = proof
  compute
  intros
  rewrite sym (plusSuccRightSucc j j)
  trivial

theorem.plusred_Z_S = proof
  intros
  rewrite ih
  trivial

theorem.plusred_Z_Z = proof
  compute
  refine Refl
