module Hashset where

open import Agda.Builtin.Nat
    using (_+_; _*_; Nat; suc; zero)
open import Data.Nat.DivMod
open import Data.Vec
open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
open import Fin
open import LinkedList

-- We are to prove: 
-- that when we put/remove, the hash number stays the same 

data _≤_ : Nat → Nat → Set where -- https://plfa.inf.ed.ac.uk/Relations/#:~:text=The%20relation%20less%20than%20or,2%202%20%E2%89%A4%203%20...
  z≤n : ∀ {n : Nat}
      --------
    → zero ≤ n
  s≤s : ∀ {m n : Nat}
    → m ≤ n
      -------------
    → suc m ≤ suc n

record Hashset (n : Nat) : Set where  -- n represents the capacity
    constructor
        hashset
    field
        buckets : Vec (LinkedList Nat) n -- Vec's that store the linked lists  
        not-zero : 1 ≤ n -- the capacity must be at least 1

mod : Nat → (n : Nat) → Fin (suc n)
mod zero _ = zero
mod (suc m) n = increment (mod m n)

-- return the index that the new set member should be placed in
-- since we're only storing Nats, the hash code is simply the Nat, and we use mod to compute the bucket/index to store it in
hash-index : {n : Nat} → (x : Nat) → Hashset n → Fin n 
hash-index {suc n} x (hashset b nz) = mod x n

-- temp add function (taken from linkedlist) ...I kept forgetting what went into add (Ellen)   
temp_add : Nat → LinkedList Nat → LinkedList Nat 
temp_add x [] = node [] x
temp_add e (node xs x) with nat-dec e x
... | yes _ = node xs x
... | no _ = node (add e xs) x

vec-apply : {A : Set} → {n : Nat} → Fin n → (A → A) → Vec A n → Vec A n
vec-apply zero f (x ∷ xs) = f x ∷ xs
vec-apply (suc a) f (x ∷ xs) = x ∷ vec-apply a f xs

put : {n : Nat} → (x : Nat) → Hashset n → Hashset n
put x (hashset b nz) = hashset (vec-apply (hash-index x (hashset b nz)) (add x) b) nz

retrieve : {n : Nat} → (x : Nat) → Hashset n → Nat
retrieve x (hashset b nz) = {!   !}
-- retrieve x (hashset b nz) = x --umm.. 90% sure this is incorrect. This is indeed incorrect.

revoke : {n : Nat} → (x : Nat) → Hashset n → Hashset n
revoke x (hashset b nz) = hashset (vec-apply (hash-index x (hashset b nz)) (LinkedList.remove x) b) nz


-- checking if in linkedlist 
mem-bool :  Nat → LinkedList Nat → Bool
mem-bool  x [] = false 
mem-bool x ( node xs y ) with nat-dec x y 
... | yes _ = true
... | no _ = mem-bool x xs 


is-member : {n : Nat} → (x : Nat) → Hashset n → Bool
is-member zero (hashset b nz) = {!   !}
is-member (suc x) (hashset b nz) = {!   !} 


-- inserting the same item more than once always produces the same hashset (i.e. subsequent insertions of 'x' will not change anything)
idempotency : {n : Nat} → (x : Nat) → (hs : Hashset n) → put x (put x hs) ≡ put x hs
idempotency zero a  = {!   !}
idempotency (suc x) (hashset b nz) = {!   !}  