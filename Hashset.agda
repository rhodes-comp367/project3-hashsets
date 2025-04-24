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

--applying Nat into Vector 

vec-apply : {A : Set} → {n : Nat} → Fin n → (A → A) → Vec A n → Vec A n
vec-apply (hash-index x y)  = {!  !} 

put : {n : Nat} → (x : Nat) → Hashset n → Hashset n
put x (hashset b nz) = hashset (vec-apply (hash-index {!   !}   {!   !}) (add x) b) nz

retrieve : {n : Nat} → (x : Nat) → Hashset n → Nat
retrieve = {!   !}

revoke : {n : Nat} → (x : Nat) → Hashset n → Hashset n
revoke = {!   !}

is-member : {n : Nat} → (x : Nat) → Hashset n → Bool
is-member = {!   !}

-- inserting the same item more than once always produces the same hashset (i.e. subsequent insertions of 'x' will not change anything)
idempotency : {n : Nat} → (x : Nat) → (hs : Hashset n) → put x (put x hs) ≡ put x hs
idempotency x (hashset b nz) = {!    !} 