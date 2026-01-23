```
module LengthAppend where
```

As a preview for what's coming this semester, here is an example of
proving a simple property of a function in a proof assistant.
Don't worry if this doesn't all make sense yet --- we will build up to this
over the next couple of weeks.

# Basic Definitions

## Natural numbers

This defines the natural numbers as a datatype, with constructors Z
(zero) and S (successor, meaning the next natural number after its
input).    

```
  data Nat : Set where 
    Z : Nat
    S : Nat → Nat 

  {-# BUILTIN NATURAL Nat #-}
```

Next, we define addition by recursion:

```
  _+_ : Nat → Nat → Nat
  Z + m = m
  S n + m = S (n + m)
```

## Equality

We'll write x == y for equality between x and y 

```
  data _==_ {A : Set} (x : A) : A → Set where
    Refl : x == x
```

This little lemma says that if n equals m then S n also equals S m.

```
  S-cong : ∀ n m → n == m → (S n == S m)
  S-cong _ _ Refl = Refl
```

# Extrinsic Verification

First, we define lists (whose elements are natural numbers) as a
datatype:

```
  data List : Set where
    [] : List
    _::_ : Nat → List → List
```

Here are some examples:
```
  example : List
  example = 1 :: (2 :: (3 :: []))

  example2 : List
  example2 = 4 :: (5 :: (6 :: []))
```

Here's an example function:
```
  length : List → Nat
  length [] = 0
  length (x :: l) = S (length l)
```

Now let's write the append function:
```
  append : List → List → List
  append [] ys = ys
  append (x :: xs) ys = x :: (append xs ys)
```

Here is a simple theorem relating the two, which came up in COMP212 when
reasoning about the time cost of sorting algorithms:
```
  length-append : ∀ xs ys → length(append xs ys) == (length xs + length ys)
  length-append [] ys = Refl
  length-append (x :: xs) ys = S-cong _ _ (length-append xs ys)
```

# Intrinsic Verification

Here is another way to organize this whole development.  Instead of
defining a regular list type, and then looking at the *property* that
its length is what it should be, we can do this reasoning directly in
the type of function, unifying the code and its proof.

```
  data ListOfLength : Nat → Set where
    [] : ListOfLength 0
    _::_ : ∀ {n} → Nat → ListOfLength n → ListOfLength (S n)
```

The [] constructor now says that the empty list has length 0.  The ::
constructor now says that it takes aa list of length n and produces a
list of length 1+n.

Now the append function's type is more precise; it tells you how append
transforms the length of the list:

```
  append2 : ∀ {n m} → ListOfLength n → ListOfLength m → ListOfLength (n + m)
  append2 [] ys = ys
  append2 (x :: xs) ys = x :: append2 xs ys
```

In this case, Agda was able to check that this property holds when type
checking the function's definition.  In other case, you will need to add
some proof steps to the code.  

