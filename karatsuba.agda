import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _⊓_ )
open import Data.Nat.DivMod
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Integer.Base 
open import Data.Integer.Properties
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import Level using (Level)



-------------------------------
-- Lists
-------------------------------

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_



pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[]       ++ ys  =  ys
(x ∷ xs) ++ ys  =  x ∷ (xs ++ ys)

++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs =
  begin
    [] ++ xs
  ≡⟨⟩
    xs
  ∎

++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] =
  begin
    [] ++ []
  ≡⟨⟩
    []
  ∎
++-identityʳ (x ∷ xs) =
  begin
    (x ∷ xs) ++ []
  ≡⟨⟩
    x ∷ (xs ++ [])
  ≡⟨ cong (x ∷_) (++-identityʳ xs) ⟩
    x ∷ xs
  ∎

++-assoc : ∀ {A : Set} (xs ys zs : List A)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs =
  begin
    ([] ++ ys) ++ zs
  ≡⟨⟩
    ys ++ zs
  ≡⟨⟩
    [] ++ (ys ++ zs)
  ∎
++-assoc (x ∷ xs) ys zs =
  begin
    (x ∷ xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ (xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ ((xs ++ ys) ++ zs)
  ≡⟨ cong (x ∷_) (++-assoc xs ys zs) ⟩
    x ∷ (xs ++ (ys ++ zs))
  ≡⟨⟩
    x ∷ xs ++ (ys ++ zs)
  ∎

length : ∀ {A : Set} → List A → ℕ
length []        =  zero
length (x ∷ xs)  =  ℕ.suc (length xs)

reverse : ∀ {A : Set} → List A → List A
reverse []        =  []
reverse (x ∷ xs)  =  reverse xs ++ [ x ]

shunt : ∀ {A : Set} → List A → List A → List A
shunt []       ys  =  ys
shunt (x ∷ xs) ys  =  shunt xs (x ∷ ys)


reverse-++-distrib : ∀ {A : Set} (xs ys : List A)
  → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-distrib [] ys =
  begin
    reverse ([] ++ ys)
  ≡⟨⟩
    reverse ys
  ≡⟨ sym ( ++-identityʳ (reverse ys) ) ⟩
    reverse ys ++ []
  ≡⟨⟩
   reverse ys ++ reverse []
  ∎
  
reverse-++-distrib (x ∷ xs) ys = 
  begin
    reverse ((x ∷ xs) ++ ys)
  ≡⟨⟩
    reverse (x ∷ (xs ++ ys))
  ≡⟨⟩
    reverse (xs ++ ys) ++ [ x ]
  ≡⟨ cong ( _++ [ x ]) (reverse-++-distrib xs ys) ⟩
    (reverse ys ++ reverse xs) ++ [ x ]
  ≡⟨ ++-assoc (reverse ys) (reverse xs) ([ x ]) ⟩
    reverse ys ++ (reverse xs ++ [ x ])
  ≡⟨⟩
    reverse ys ++ reverse (x ∷ xs)
  ∎

reverse-involutive : ∀ {A : Set } (xs : List A) 
  → reverse (reverse xs) ≡ xs 
reverse-involutive [] =
  begin
    reverse (reverse [])  
  ≡⟨⟩
    reverse ([])
    ≡⟨⟩
    []
  ∎
reverse-involutive (x ∷ xs) =
  begin
    reverse (reverse (x ∷ xs))
  ≡⟨⟩
    reverse ( reverse xs ++ [ x ])
  ≡⟨ reverse-++-distrib (reverse xs) [ x ] ⟩
    reverse [ x ] ++ reverse (reverse xs)
  ≡⟨⟩
    reverse (x ∷ []) ++ reverse (reverse xs)
  ≡⟨⟩
    reverse [] ++ [ x ] ++ reverse (reverse xs)
  ≡⟨⟩  
    [ x ] ++ reverse (reverse xs)
  ≡⟨ cong ( [ x ] ++_ ) (reverse-involutive xs)⟩
    [ x ] ++ xs
  ≡⟨⟩
    x ∷ xs
  ∎


----------------------------------
----------------------------------
-- functions

map : ∀ {A B : Set} → (A → B) → List A → List B
map f []        =  []
map f (x ∷ xs)  =  f x ∷ map f xs

reverse′ : ∀ {A : Set} → List A → List A
reverse′ xs = shunt xs []

take : ∀ {A : Set} → ℕ → List A → List A
take _ [] = []
take zero _ = []
take (suc n) (x ∷ xs) = x ∷ take n xs

drop : ∀ {A : Set} → ℕ → List A → List A
drop (suc n) (x ∷ xs) = drop n xs
drop zero xs = xs
drop n [] = []
  
replicate : ∀ {A : Set} → ℕ → A → List A
replicate zero _ = []
replicate (suc n) x = x ∷ replicate n x


shift_right : ℕ → List ℤ → List ℤ
shift_right n xs = (replicate n +0) ++ xs

addPoly : List ℤ → List ℤ → List ℤ
addPoly xs [] = []
addPoly [] ys = []
addPoly (x ∷ xs) (y ∷ ys) = x + y ∷ addPoly xs ys

record Pair (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

{-# COMPILE GHC Pair = data (,) ((,)) #-}


splitAt : ∀ {A : Set} → ℕ → List A →  Pair (List A) (List A) 
splitAt n xs = ( take n xs , drop n xs ) 

mulPoly : List ℤ → List ℤ → List ℤ
mulPoly [] ys = []
mulPoly xs [] = []
mulPoly (x ∷ xs) ys = addPoly (map (x *_) ys) (+0 ∷ mulPoly xs ys)

negPoly : List ℤ → List ℤ
negPoly [] = []
negPoly (x ∷ xs) = (- x) ∷ negPoly xs

subPoly : List ℤ → List ℤ → List ℤ
subPoly xs ys = addPoly xs (negPoly ys)



a : List ℤ
a = [ + 2 , + 1 ]

b : List ℤ
b = [ + 1 , + 2 ]

--------------------------
--------------------------
-- Karatsuba



karatsuba : ℕ → List ℤ → List ℤ → List ℤ
karatsuba n [] xs = []
karatsuba n ys [] = []
karatsuba n [ x ] ys = map (x *_) ys
karatsuba n xs [ y ] = map (y *_) xs
karatsuba n (x1 ∷ x2 ∷ []) ys = mulPoly (x1 ∷ x2 ∷ []) ys
karatsuba n xs (y1 ∷ y2 ∷ []) = mulPoly xs (y1 ∷ y2 ∷ [])
karatsuba n xs ys = let m = ((length xs / 2) Data.Nat.⊓ (length ys / 2)) in
                  let ba = splitAt m xs in
                  let dc = splitAt m ys in
                  let ac = karatsuba n (Pair.snd ba) (Pair.snd dc) in 
                  let bd = karatsuba n (Pair.fst ba) (Pair.fst dc) in
                  let a_plus_b = addPoly (Pair.snd ba) (Pair.fst ba) in
                  let c_plus_d = addPoly (Pair.snd dc) (Pair.fst dc) in
                  let ad_plus_bc = (subPoly (subPoly (karatsuba n a_plus_b c_plus_d) ac) bd) in
                  addPoly (addPoly (shift_right (2 Data.Nat.* m) ac) (shift_right m ad_plus_bc)) bd


karatsuba' : List ℤ → List ℤ → List ℤ
karatsuba' xs ys = karatsuba ((length xs) Data.Nat.⊓ (length ys)) xs ys
