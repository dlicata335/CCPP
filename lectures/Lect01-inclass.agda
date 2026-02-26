module LengthAppend-starter where

  -- equality
  data _==_ {A : Set} (x : A) : A → Set where
    Refl : x == x

  data Nat : Set where
    Z : Nat
    S : Nat → Nat

  {-# BUILTIN NATURAL Nat #-}

  zero : Nat
  zero = Z

  one : Nat
  one = S Z

  five : Nat
  five = S (S (S (S (S Z))))

  plus : Nat → Nat → Nat
  plus Z m = m
  plus (S n) m = S (plus n m)

  1+-cong : ∀ n m → n == m → (S n == S m)
  1+-cong _ _ Refl = Refl

  five= : 5 == 5
  five= = 1+-cong _ _ Refl 

  -- lists of natural numbers
  data List : Set where
    [] : List
    _::_ : Nat → List → List

  example1 = 1 :: (2 :: (3 :: []))
  example2 = 4 :: (5 :: (6 :: []))

  length : List → Nat
  length [] = 0
  length (x :: xs) = S (length xs)

  append : List → List → List
  append [] ys = ys
  append (x :: xs) ys = x :: append xs ys

  example3 = plus 5 5

  example3-test : (plus 5 5) == 10
  example3-test = Refl

  -- example3-test2 : (plus 5 5) == 9
  -- example3-test2 = {!!}

  _+_ = plus

  theorem : ∀ (xs ys : List) →
            length (append xs ys) ==
            ((length xs) + (length ys))
  theorem [] ys = Refl
  theorem (x :: xs') ys = 1+-cong _ _ (theorem xs' ys)


  -- pretend the above doesn't exist...

  -- Intrinsic verification
  data ListOfLength : Nat → Set where
    [] : ListOfLength 0 
    _::_ : ∀ {n} → Nat → ListOfLength n → ListOfLength (S n)

  append2 : ∀ {n m}
          → ListOfLength n → ListOfLength m → ListOfLength (n + m)
  append2 [] ys = ys
  append2 (x :: xs) ys = x :: (append2 xs ys)

  
