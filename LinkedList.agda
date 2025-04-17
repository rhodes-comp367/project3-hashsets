module LinkedList where

open import Agda.Builtin.Nat

data LinkedList (A : Set) : Set where
    emp : LinkedList A
    node : LinkedList A → A → LinkedList A -- node adds A to the end of the linked list

-- prepend an element to the front of a list.
prepend : {A : Set} → A → LinkedList A → LinkedList A 
prepend x emp = node emp x
prepend y (node xs x) = node (prepend y xs) x

-- number of nodes in a linked list
size : {A : Set} → LinkedList A → Nat
size emp = 0
size (node xs x) = 1 + (size xs)

