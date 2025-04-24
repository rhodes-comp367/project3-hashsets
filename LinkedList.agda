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

data Element {A : Set} (x : A) : LinkedList A → Set where
  last : ∀ {xs} → Element x (node xs x)
  init : ∀ {xs y} → Element x xs → Element x (node xs y)

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

~ : Set → Set
~ A = A → ⊥

data Dec (A : Set) : Set where
  yes : A → Dec A
  no : ~ A → Dec A

-- natural number equality is decidable
nat-dec : (m n : Nat) → Dec (m ≡ n)
nat-dec zero zero = yes refl
nat-dec zero (suc _) = no (λ ())
nat-dec (suc _) zero = no (λ ())
nat-dec (suc m) (suc n) with nat-dec m n
... | yes refl = yes refl
... | no p = no (λ {refl → p refl})

-- add a Nat to the list. 
add : Nat → LinkedList Nat → LinkedList Nat -- ChatGPT suggested for me to use a function within to compare two values
add x [] = node [] x
add e (node xs x) with nat-dec e x
... | yes _ = node xs x
... | no _ = node (add e xs) x

contains' : (x : Nat) → (xs : LinkedList Nat) → Dec (Element x xs)
contains' = ?

-- check for existence of a Nat
contains : Nat → LinkedList Nat → Bool
contains x [] = false
contains e (node xs x) with nat-dec e x
... | yes _ = true
... | no _ = contains e xs

-- number of nodes in a linked list
size : LinkedList Nat → Nat
size [] = 0
size (node xs x) = 1 + (size xs)

remove : (x : Nat) → LinkedList Nat → LinkedList Nat
remove x [] = []
remove e (node xs x) with nat-dec e x
... | yes _ = xs
... | no _ = node (remove e xs) x

-- removing the first item from a list  
removeFirst : LinkedList Nat → LinkedList Nat
removeFirst [] = []
removeFirst (node [] x) = []
removeFirst (node xs x) = node (removeFirst xs) x

--removing the last item from a list (x) 
removeLast : LinkedList Nat → LinkedList Nat
removeLast [] = [] 
removeLast (node xs x) = xs 

remove-last-node : (x : Nat) → (xs : LinkedList Nat) → xs ≡ (removeLast (node xs x))
remove-last-node _ _ = refl

-- linked list contains element after being added in 
add-contains : ∀ n ns → contains n (add n ns) ≡ true
add-contains n [] with nat-dec n n
... | yes _ = refl
... | no ~e = ⊥-elim (~e refl)
add-contains n (node ns x) with nat-dec n x 
add-contains n (node ns x) | yes refl with nat-dec n n 
...   | yes _ = refl
...   | no ~e = ⊥-elim (~e refl)
add-contains n (node ns x) | no _ with nat-dec n x
...   | yes _ = refl
...   | no ~e = add-contains n ns



-- remove-contains

add-element : ∀ x xs → Element x (add x xs)
add-element = ?

remove-add : {x : Nat} → {xs : LinkedList Nat} → Element x xs → add x (remove x xs) ≡ xs
remove-add = {!   !}

-- adding then removing returns the same linked list
add-remove : (x : Nat) → (xs : LinkedList Nat) → remove x xs ≡ remove x (add x xs)
add-remove x [] with nat-dec x x
... | yes _ = refl
... | no ~e = ⊥-elim (~e refl)

add-remove e (node xs x) with nat-dec e x
add-remove e (node xs x) | yes refl with nat-dec e x
...   | yes refl = {!    !}
...   | no ~e = {!   !} 
add-remove e (node xs x) | no _ with nat-dec e x
...   | yes _ = {!   !}
...   | no ~e = {!   !}


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
 