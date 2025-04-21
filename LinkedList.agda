-- LinkedList data structure that only stores Nats --

{-# OPTIONS --allow-unsolved-metas #-}

module LinkedList where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

data Nat= : Nat → Nat → Set where
  zero= : Nat= zero zero
  suc= : ∀ {m n} → Nat= m n → Nat= (suc m) (suc n)

data LinkedList (A : Set) : Set where
    [] : LinkedList A
    node : LinkedList A → A → LinkedList A -- add A to the end of the linked list

data LinkedList= : LinkedList Nat → LinkedList Nat → Set where 
    []= : LinkedList= [] []
    node= : {x y : Nat} → {xs ys : LinkedList Nat} 
        → Nat= x y → LinkedList= xs ys → LinkedList= (node xs x) (node ys y)

-- add a Nat to the list. 
add : Nat → LinkedList Nat → LinkedList Nat -- ChatGPT suggested for me to use a function within to compare two values
add x [] = node [] x
add e (node xs x) with e == x
... | true = node xs x
... | false = node (add e xs) x


-- number of nodes in a linked list
size : LinkedList Nat → Nat
size [] = 0
size (node xs x) = 1 + (size xs)

-- removing the first item from a list  
removeFirst : LinkedList Nat → LinkedList Nat

removeFirst [] = []
removeFirst (node [] x) = []
removeFirst (node xs x) = node (removeFirst xs) x

--removing the last item from a list (x) 
removeLast : LinkedList Nat → LinkedList Nat
removeLast [] = [] 
-- need to change this to reflect removing last 
-- need to figure out how to add x to the end 
-- add f x []
removeLast (node xs x) = xs 


-- Ellen's crashout ... ignore below
-- checking if the numbers are equal + that we are removing the correct node 
-- mostly chat code, and noting here that we may have problems if there are nodes with same Nats

-- natEq : Nat → Nat → Bool 
-- natEq zero zero = true
-- natEq (suc n) (suc m) = natEq n m
-- natEq _ _ = false

-- removeFirst : {A : Set} → (x : A) → (xs : LinkedList A) → (A → A → Bool) → LinkedList A -- chat helped me figure out the starting cases
-- base case
-- removeFirst x [] natEq = []
-- removing element in end of list 
-- removeFirst x (y :: ys) natEq with natEq x y
-- ... | true  = ys
-- ... | false = y :: remove x ys natEq

-- removing element at end of list 
-- removing element in the middle of list 
