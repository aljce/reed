module Fields where

open import Agda.Builtin.Equality
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat using (Nat ; zero ; suc)
open import Agda.Builtin.FromNat

data ⊥ : Set where

¬_ : Set -> Set
¬ A = A -> ⊥

qed : ∀ {A : Set} -> (x : A) -> x ≡ x
qed _ = refl

infixr 2 _[_]_
_[_]_ : ∀ {A : Set} {y z : A} -> (x : A) -> x ≡ y -> y ≡ z -> x ≡ z
_ [ refl ] refl = refl

infixl 2 _~_
_~_ : ∀ {A : Set} {a b c : A} -> a ≡ b -> b ≡ c -> a ≡ c
refl ~ refl = refl

sym : ∀ {A : Set} {x y : A} -> x ≡ y -> y ≡ x
sym refl = refl

cong : ∀ {A B : Set} {x y : A} -> (f : A -> B) -> x ≡ y -> f x ≡ f y
cong _ refl = refl

record Identity {F : Set} (e : F) (op : F -> F -> F) : Set where
  field
    left-identity : ∀ (a : F) -> op e a ≡ a
    right-identity : ∀ (a : F) -> op a e ≡ a

record Inverse {F : Set} (e : F) (op : F -> F -> F) (inv : F -> F) : Set where
  field
    left-inverse : ∀ (x : F) -> op (inv x) x ≡ e
    right-inverse : ∀ (x : F) -> op x (inv x) ≡ e

record Field (F : Set) : Set where
  infixl 6 _+_
  infixl 7 _·_
  field
    0# : F
    _+_ : F -> F -> F
    +-assoc : ∀ (a b c : F) -> a + (b + c) ≡ (a + b) + c
    +-0-identity : Identity 0# _+_
    -_ : F -> F
    +-0-inverse : Inverse 0# _+_ -_
    1# : F
    _·_ : F -> F -> F
    ·-comm : ∀ (a b : F) -> a · b ≡ b · a
    ·-assoc : ∀ (a b c : F) -> a · (b · c) ≡ (a · b) · c
    ·-1-identity : Identity 1# _·_
    _⁻¹ : F -> F
    ·-1-inverse : Inverse 1# _·_ _⁻¹
    +-·-dist : ∀ (a b c : F) -> a · (b + c) ≡ (a · b) + (a · c)
    0≠1 : ¬ (0# ≡ 1#)

module FieldTheorems {F : Set} (f : Field F) where
  open Field f
  open Identity +-0-identity renaming
    ( left-identity to +-left-identity
    ; right-identity to +-right-identity )
  open Identity ·-1-identity renaming
    ( left-identity to ·-left-identity
    ; right-identity to ·-right-identity )
  open Inverse +-0-inverse renaming
    ( left-inverse to +-left-inverse
    ; right-inverse to +-right-inverse )
  open Inverse ·-1-inverse renaming
    ( left-inverse to ·-left-inverse
    ; right-inverse to ·-right-inverse )


  instance
    FieldNumber : Number F
    FieldNumber =
      record { Constraint = λ _ → ⊤
             ; fromNat = natToField }
      where
      natToField : Nat -> {{_ : ⊤}} -> F
      natToField 0 = 0#
      natToField 1 = 1#
      natToField 2 = 1# + 1#
      natToField (suc (suc n)) = (natToField n + 1#) + 1#

  infixl 6 _-_
  _-_ : F -> F -> F
  x - y = x + (- y)

  +-cancellation-equality : ∀ {x y : F} -> x - y ≡ 0 -> x ≡ y
  +-cancellation-equality {x} {y} x-y≡0 =
    sym lemma ~ cong (λ t -> t + y) x-y≡0 ~ +-left-identity y
    where
    lemma : (x - y) + y ≡ x
    lemma =
      (x + (- y)) + y [ sym (+-assoc x (- y) y) ]
      x + ((- y) + y) [ cong (λ z → x + z) (+-left-inverse y) ]
      x + 0 [ +-right-identity x ]
      qed x

  postulate
    +-double-inverse : ∀ (x : F) -> - (- x) ≡ x

    +-0-destructive : ∀ (x : F) -> x · 0 ≡ 0

  2-77-a :  ∀ (a b : F) -> (- a) · b ≡ - (a · b)
  2-77-a a b = +-cancellation-equality lemma
    where
    sub-lemma : - (- (a · b)) ≡ b · a
    sub-lemma =
      - (- (a · b)) [ +-double-inverse (a · b) ]
      a · b [ ·-comm a b ]
      qed (b · a)

    lemma : ((- a) · b) + (- (- (a · b))) ≡ 0
    lemma =
      ((- a) · b) + (- (- (a · b))) [ cong (λ t → ((- a) · b) + t) sub-lemma ]
      ((- a) · b) + (b · a)         [ cong (λ t -> t + (b · a)) (·-comm (- a) b)]
      (b · (- a)) + (b · a)         [ sym (+-·-dist b (- a) a) ]
      b · ((- a) + a)               [ cong (λ t -> b · t) (+-left-inverse a) ]
      b · 0                         [ +-0-destructive b ]
      qed 0

  2-76 : ∀ (a b : F) -> a · (- b) ≡ - (a · b)
  2-76 a b =
    a · (- b) [ ·-comm a (- b) ]
    (- b) · a [ 2-77-a b a ]
    - (b · a) [ cong (-_) (·-comm b a) ]
    qed (- (a · b))

  2-77-b : ∀ (a : F) -> a · (- 1#) ≡ - a
  2-77-b a =
    a · (- 1#) [ ·-comm a (- 1#) ]
    (- 1#) · a [ 2-77-a 1# a ]
    - (1# · a) [ cong (-_) (·-left-identity a) ]
    qed (- a)

  2-85-a : 3 + 3 ≡ 6
  2-85-a =
    3 + ((1 + 1) + 1) [ +-assoc 3 (1 + 1) 1 ]
    (3 + (1 + 1)) + 1 [ cong (λ t -> t + 1) (+-assoc 3 1 1) ]
    qed (((3 + 1) + 1) + 1)

  2-88 : ∀ (x : F) -> 2 · x ≡ x + x
  2-88 x =
    2 · x             [ ·-comm 2 x                                     ]
    x · (1 + 1)       [ +-·-dist x 1 1                                 ]
    (x · 1) + (x · 1) [ cong (λ t -> t + (x · 1)) (·-right-identity x) ]
    x + (x · 1)       [ cong (λ t -> x + t) (·-right-identity x)       ]
    qed (x + x)

  2-85-b : 3 · 2 ≡ 6
  2-85-b =
    3 · 2 [ ·-comm 3 2 ]
    2 · 3 [ 2-88 3     ]
    3 + 3 [ 2-85-a     ]
    qed 6

  2-90-a : ∀ (a b c : F) -> a · (b - c) ≡ a · b - a · c
  2-90-a a b c =
    a · (b + (- c)) [ +-·-dist a b (- c) ]
    (a · b) + (a · (- c)) [ cong (λ t -> (a · b) + t) lemma ]
    qed ((a · b) - (a · c))
    where
    lemma : a · (- c) ≡ - (a · c)
    lemma =
      a · (- c) [ ·-comm a (- c) ]
      (- c) · a [ 2-77-a c a ]
      - (c · a) [ cong (-_) (·-comm c a) ]
      qed (- (a · c))

  2-90-b : ∀ (a b : F) -> - (a - b) ≡ b - a
  2-90-b a b = sym (+-cancellation-equality lemma)
    where
    remove-a : ∀ (x : F) -> (- a) + (a + x) ≡ x
    remove-a x =
      (- a) + (a + x) [ +-assoc (- a) a x ]
      ((- a) + a) + x [ cong (λ t → t + x) (+-left-inverse a) ]
      0# + x [ +-left-identity x ]
      qed x
    lemma : (b - a) - (- (a - b)) ≡ 0#
    lemma =
      (b - a) + (- (- (a - b))) [ cong (λ t → (b - a) + t) (+-double-inverse (a - b)) ]
      (b + (- a)) + (a + (- b)) [ sym (+-assoc b (- a) (a + (- b))) ]
      (b + ((- a) + (a + (- b)))) [ cong (λ t → b + t) (remove-a (- b)) ]
      b + (- b) [ +-right-inverse b ]
      qed 0#

  infixl 7 _/_
  _/_ : F -> F -> F
  a / b = a · (b ⁻¹)

  postulate
    ·-inverse-dist : ∀ (a b : F) -> (a · b) ⁻¹ ≡ a ⁻¹ · b ⁻¹

  2-93-b : ∀ (a b d : F) -> (d · a) / (d · b) ≡ a / b
  2-93-b a b d =
    (d · a) · (d · b) ⁻¹   [ cong (λ t -> (d · a) · t)  (·-inverse-dist d b) ]
    (d · a) · (d ⁻¹ · b ⁻¹) [ cong (λ t -> t · (d ⁻¹ · b ⁻¹)) (·-comm d a) ]
    (a · d) · (d ⁻¹ · b ⁻¹) [ sym (·-assoc a d (d ⁻¹ · b ⁻¹)) ]
    a · (d · (d ⁻¹ · b ⁻¹)) [ cong (λ t -> a · t) (remove-d (b ⁻¹)) ]
    qed (a / b)
    where
    remove-d : ∀ (x : F) -> d · (d ⁻¹ · x) ≡ x
    remove-d x =
      d · (d ⁻¹ · x) [ ·-assoc d (d ⁻¹) x ]
      (d · d ⁻¹) · x [ cong (λ t -> t · x) (·-right-inverse d) ]
      1 · x [ ·-left-identity x ]
      qed x

  2-93-e : ∀ (a b c d : F) -> (a · d + b · c) / (b · d) ≡ a / b + c / d
  2-93-e a b c d =
    (a · d + b · c) · (b · d) ⁻¹ [ cong (λ t -> (a · d + b · c) · t) (·-inverse-dist b d) ]
    (a · d + b · c) · (b ⁻¹ · d ⁻¹) [ ·-comm (a · d + b · c) (b ⁻¹ · d ⁻¹) ]
    (b ⁻¹ · d ⁻¹) · (a · d + b · c) [ +-·-dist (b ⁻¹ · d ⁻¹) (a · d) (b · c) ]
    (b ⁻¹ · d ⁻¹) · (a · d) + (b ⁻¹ · d ⁻¹) · (b · c) [ cong (λ t -> t + (b ⁻¹ · d ⁻¹) · (b · c)) lemma-a/b ]
    a / b + (b ⁻¹ · d ⁻¹) · (b · c) [ cong (λ t -> a / b + t) lemma-c/d ]
    qed (a / b + c / d)
    where
    lemma-a/b : (b ⁻¹ · d ⁻¹) · (a · d) ≡ a / b
    lemma-a/b =
      (b ⁻¹ · d ⁻¹) · (a · d) [ ·-comm (b ⁻¹ · d ⁻¹) (a · d) ]
      (a · d) · (b ⁻¹ · d ⁻¹) [ sym (·-assoc a d (b ⁻¹ · d ⁻¹)) ]
      a · (d · (b ⁻¹ · d ⁻¹)) [ cong (λ t -> a · t) (sub-lemma-a/b (b ⁻¹)) ]
      qed (a / b)
      where
      sub-lemma-a/b : ∀ (x : F) -> d · (x · d ⁻¹) ≡ x
      sub-lemma-a/b x =
        d · (x · d ⁻¹) [ cong (λ t -> d · t) (·-comm x (d ⁻¹)) ]
        d · (d ⁻¹ · x) [ ·-assoc d (d ⁻¹) x ]
        (d · d ⁻¹) · x [ cong (λ t -> t · x) (·-right-inverse d) ]
        1 · x [ ·-left-identity x ]
        qed x
    lemma-c/d : (b ⁻¹ · d ⁻¹) · (b · c) ≡ c / d
    lemma-c/d =
      (b ⁻¹ · d ⁻¹) · (b · c) [ ·-comm (b ⁻¹ · d ⁻¹) (b · c)]
      (b · c) · (b ⁻¹ · d ⁻¹) [ cong (λ t -> t · (b ⁻¹ · d ⁻¹)) (·-comm b c) ]
      (c · b) · (b ⁻¹ · d ⁻¹) [ sym (·-assoc c b (b ⁻¹ · d ⁻¹)) ]
      c · (b · (b ⁻¹ · d ⁻¹)) [ cong (λ t -> c · t) (sub-lemma-c/d (d ⁻¹)) ]
      qed (c / d)
      where
      sub-lemma-c/d : ∀ (x : F) -> b · (b ⁻¹ · x) ≡ x
      sub-lemma-c/d x =
        b · (b ⁻¹ · x) [ ·-assoc b (b ⁻¹) x ]
        (b · b ⁻¹) · x [ cong (λ t -> t · x) (·-right-inverse b) ]
        1 · x         [ ·-left-identity x ]
        qed x

  _² : F -> F
  x ² = x · x

  2-94-a : ∀ (a b : F) -> (a + b) ² ≡ a ² + 2 · a · b + b ²
  2-94-a a b =
    (a + b) · (a + b)               [ +-·-dist (a + b) a b ]
    ((a + b) · a) + ((a + b) · b)   [ cong (λ t -> t + ((a + b) · b)) lemma-a ]
    (a ² + a · b) + ((a + b) · b)   [ cong (λ t -> (a ² + a · b) + t) lemma-b ]
    (a ² + a · b) + (a · b + b ²)   [ sym (+-assoc (a ²) (a · b) (a · b + b ²)) ]
    a ² + ((a · b) + (a · b + b ²)) [ cong (λ t -> a ² + t) lemma-c ]
    a ² + (2 · a · b + b ²)         [ +-assoc (a ²) (2 · a · b) (b ²) ]
    qed (a ² + 2 · a · b + b ²)
    where
    lemma-a : (a + b) · a ≡ a ² + a · b
    lemma-a =
      (a + b) · a [ ·-comm (a + b) a ]
      a · (a + b) [ +-·-dist a a b ]
      qed (a ² + a · b)
    lemma-b : (a + b) · b ≡ a · b + b ²
    lemma-b =
      (a + b) · b [ ·-comm (a + b) b ]
      b · (a + b) [ +-·-dist b a b ]
      (b · a) + b ² [ cong (λ t -> t + b ²) (·-comm b a) ]
      qed (a · b + b ²)
    lemma-c : (a · b) + (a · b + b ²) ≡ 2 · a · b + b ²
    lemma-c =
      (a · b) + (a · b + b ²) [ +-assoc (a · b) (a · b) (b ²) ]
      (a · b + a · b) + b ² [ cong (λ t -> t + b ²) sub-lemma-c ]
      qed (2 · a · b + b ²)
      where
      sub-lemma-c : (a · b + a · b) ≡ 2 · a · b
      sub-lemma-c =
        a · b + a · b [ sym (2-88 (a · b)) ]
        2 · (a · b)   [ ·-assoc 2 a b ]
        qed (2 · a · b)

  2-94-c : ∀ (a b : F) -> (a - b) · (a + b) ≡ a ² - b ²
  2-94-c a b =
    (a - b) · (a + b) [ +-·-dist (a - b) a b ]
    (a - b) · a + (a - b) · b [ cong (λ t -> t + (a - b) · b) lemma-a ]
    a ² - a · b + (a - b) · b [ cong (λ t -> a ² - a · b + t) lemma-b ]
    a ² + (- (a · b)) + (a · b - b ²) [ sym (+-assoc (a ²) (- (a · b)) (a · b - b ²) ) ]
    a ² + ((- (a · b)) + (a · b - b ²)) [ cong (λ t -> a ² + t) lemma-cancel ]
    qed (a ² - b ²)
    where
    lemma-a : (a - b) · a ≡ a ² - a · b
    lemma-a =
      (a - b) · a [ ·-comm (a - b) a ]
      a · (a + (- b)) [ +-·-dist a a (- b) ]
      a ² + a · (- b) [ cong (λ t -> a ² + t) (2-76 a b) ]
      qed (a ² - a · b)
    lemma-b : (a - b) · b ≡ a · b - b ²
    lemma-b =
      (a - b) · b [ ·-comm (a - b) b ]
      b · (a + (- b)) [ +-·-dist b a (- b) ]
      b · a + b · (- b) [ cong (λ t -> b · a + t) (2-76 b b) ]
      b · a + (- (b ²)) [ cong (λ t -> t + (- (b ²))) (·-comm b a)]
      qed (a · b - b ²)
    lemma-cancel : (- (a · b)) + (a · b - b ²) ≡ - (b ² )
    lemma-cancel = 
      (- (a · b)) + (a · b - b ²) [ +-assoc (- (a · b)) (a · b) (- (b ²)) ]
      ((- (a · b)) + a · b) - b ² [ cong (λ t -> t - b ²) (+-left-inverse (a · b))]
      0 + (- (b ²)) [ +-left-identity (- (b ²)) ]
      qed (- (b ²))
