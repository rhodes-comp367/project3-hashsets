module LinkedList where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

data LinkedList (A : Set) : Set where
    [] : LinkedList A
    node : LinkedList A → A → LinkedList A -- node adds A to the end of the linked list

-- add an element to the front of a list. 
ll-add : {A : Set} → (A → A → Bool) → A → LinkedList A → LinkedList A -- ChatGPT suggested for me to use a function within to compare two values
ll-add f x [] = node [] x
ll-add f e (node xs x) with f e x
... | true = node xs x
... | false = node (ll-add f e xs) x


-- number of nodes in a linked list
size : {A : Set} → LinkedList A → Nat
size [] = 0
size (node xs x) = 1 + (size xs)


--Ellen's Removing Shenanigans 
-- checking if the numbers are equal + that we are removing the correct node 
-- mostly chat code, and noting here that we may have problems if there are nodes with same Nats

natEq : Nat → Nat → Bool 
natEq zero zero = true
natEq (suc n) (suc m) = natEq n m
natEq _ _ = false

-- removeFirst : {A : Set} → (x : A) → (xs : LinkedList A) → (A → A → Bool) → LinkedList A -- chat helped me figure out the starting cases
-- base case
-- removeFirst x [] natEq = []
-- removing element in end of list 
-- removeFirst x (y :: ys) natEq with natEq x y
-- ... | true  = ys
-- ... | false = y :: remove x ys natEq

-- removing element at end of list 
-- removing element in the middle of list 
