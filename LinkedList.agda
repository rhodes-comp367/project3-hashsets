-- LinkedList data structure that only stores Nats --

{-# OPTIONS --allow-unsolved-metas #-}

module LinkedList where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Data.Maybe

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
add : Nat → LinkedList Nat → LinkedList Nat
add x [] = node [] x
add e (node xs x) with nat-dec e x
... | yes _ = node xs x
... | no _ = node (add e xs) x

-- clear all elements in linked list
clear : LinkedList Nat → LinkedList Nat
clear [] = []
clear (node xs x) = []

-- return an element
get : Nat → LinkedList Nat → Maybe Nat
get x [] = nothing
get e (node xs x) with nat-dec e x 
... | yes _ = just e
... | no _ = get e xs

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
remove-first : LinkedList Nat → LinkedList Nat
remove-first [] = []
remove-first (node [] x) = []
remove-first (node xs x) = node (remove-first xs) x

--removing the last item from a list (x) 
remove-last : LinkedList Nat → LinkedList Nat
remove-last [] = [] 
remove-last (node xs x) = xs 

remove-last-node : (x : Nat) → (xs : LinkedList Nat) → xs ≡ (remove-last (node xs x))
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

idempotency-ll : (x : Nat) → (xs : LinkedList Nat) → add x (add x xs) ≡ add x xs
idempotency-ll x [] with nat-dec x x
... | yes _ = refl
... | no ~e = ⊥-elim (~e refl)
idempotency-ll e (node xs x) with nat-dec e x
idempotency-ll e (node xs x) | yes refl with nat-dec e x
... | yes _ = refl
... | no ~e = ⊥-elim (~e refl)
idempotency-ll e (node xs x) | no ~e with nat-dec e x 
... | yes _ = refl
... | no x₁ rewrite idempotency-ll e xs = refl

-- remove-contains
remove-contains : ∀ n ns → contains n (remove n ns) ≡ false 
remove-contains n [] = refl
remove-contains n (node ns x) with nat-dec n x 
... | yes _ = {!    !}
... | no ~e = {!   !}

-- removing and then adding gives back the same linked list
remove-add : {x : Nat} → {xs : LinkedList Nat} → Element x xs → add x (remove x xs) ≡ xs
remove-add {x} last with nat-dec x x
... | yes _ = {!   !}
... | no _ = {!   !}
remove-add (init x) = {!   !}

-- adding then removing returns the same linked list
add-remove : (x : Nat) → (xs : LinkedList Nat) → ~ (Element x xs) → xs ≡ remove x (add x xs)
add-remove x [] p with nat-dec x x 
... | yes _ = refl
... | no ~e = ⊥-elim (~e refl)
add-remove n (node xs x) p with nat-dec n x
add-remove n (node xs x) p | yes refl with nat-dec n x
...   | yes _ = ⊥-elim (p last)
...   | no _ = ⊥-elim (p last)
add-remove n (node xs x) p | no x₂ with nat-dec n x
...   | yes x₁ = ⊥-elim (x₂ x₁)
...   | no ~e rewrite add-remove n xs {!   !} = {!   !}

-- clearing a linked list is the same as an empty one []
clear-empty : (xs : LinkedList Nat) → [] ≡ clear xs
clear-empty [] = refl
clear-empty (node xs x) = refl
 