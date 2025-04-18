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

