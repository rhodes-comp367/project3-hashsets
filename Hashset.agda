module Hashset where

open import Agda.Builtin.Nat
    using (_+_; _*_; Nat; suc; zero)
open import Data.Nat.DivMod
open import Data.Vec
open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
open import Fin
open import LinkedList
open import Data.Maybe

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
-- hash-index 2 (hashset ((node (node [] 15) 5) ∷ (node [] 20) ∷ ((node [] 10) ∷ [])) (1≤3))

-- return the index that the new set member should be placed in
-- since we're only storing Nats, the hash code is simply the Nat, and we use mod to compute the bucket/index to store it in
mod : Nat → (n : Nat) → Fin (suc n)
mod zero _ = zero
mod (suc m) n = increment (mod m n)

1≤3 : suc zero ≤ suc (suc (suc zero))
1≤3 = s≤s z≤n

vec-apply : {A : Set} → {n : Nat} → Fin n → (A → A) → Vec A n → Vec A n
vec-apply zero f (x ∷ xs) = f x ∷ xs
vec-apply (suc a) f (x ∷ xs) = x ∷ vec-apply a f xs

put : {n : Nat} → (x : Nat) → Hashset n → Hashset n
put {suc n} x (hashset b nz) = hashset (vec-apply (mod x n) (add x) b) nz

-- Vec lookup
index :  {A : Set} {n : Nat} → Vec A n → Fin n → A
index (x ∷ xs) zero = x
index (x ∷ xs) (suc y) = index xs y 
 
retrieve : {n : Nat} → (x : Nat) → Hashset n → Maybe Nat
retrieve {suc n} x (hashset b nz) = get x (index b (mod x n))

-- retrieve x (hashset b nz) = x --umm.. 90% sure this is incorrect (ellen). This is indeed incorrect (matthew).

-- remove function
revoke : {n : Nat} → (x : Nat) → Hashset n → Hashset n
revoke {suc n} x (hashset b nz) = hashset (vec-apply (mod x n) (LinkedList.remove x) b) nz

-- contains function
is-member : {n : Nat} → (x : Nat) → Hashset n → Bool
is-member {suc n} x (hashset b nz) = contains x (index b (mod x n))

-- 'A → A' represents 'LinkedList Nat → LinkedList Nat'
index-vec-apply : {A : Set} → {n : Nat} → (k : Fin n) → (f : A → A) → (xs : Vec A n)
  → index (vec-apply k f xs) k ≡ f (index xs k)
index-vec-apply zero f (x ∷ xs) = refl
index-vec-apply (suc k) f (x ∷ xs) = index-vec-apply k f xs

-- element should be a member of hashset once put in
put-is-member : {n : Nat} → (x : Nat) → (ns : Hashset n) → is-member x (put x ns) ≡ true
put-is-member {suc n} x (hashset b nz) rewrite index-vec-apply (mod x n) (add x) b | add-contains x (index b (mod x n)) = refl

-- removing a member of the hashset then checking for membership should return false
revoke-is-member : {n : Nat} → (x : Nat) → (ns : Hashset n) → is-member x (revoke x ns) ≡ false
revoke-is-member {suc n} x (hashset b nz) rewrite index-vec-apply (mod x n) (LinkedList.remove x) b | remove-contains x (index b (mod x n)) = refl

-- inserting the same item more than once always produces the same hashset (i.e. subsequent insertions of 'x' will not change anything)
idempotency : {n : Nat} → (x : Nat) → (hs : Hashset n) → put x (put x hs) ≡ put x hs
idempotency {suc n} x (hashset b nz) = {!    !}
 