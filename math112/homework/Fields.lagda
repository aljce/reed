\documentclass{article}

\usepackage{agda}

\usepackage{amssymb}
\usepackage{bbm}
\usepackage[greek,english]{babel}

\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{autofe}

\DeclareUnicodeCharacter{8988}{\ensuremath{\ulcorner}}
\DeclareUnicodeCharacter{8989}{\ensuremath{\urcorner}}
\DeclareUnicodeCharacter{8803}{\ensuremath{\overline{\equiv}}}
\DeclareUnicodeCharacter{8718}{\ensuremath{\blacksquare}}

\title{Math 112 Thursday Homework}
\author{Kyle McKean}

\begin{document}
\maketitle

The following code is agda, a programming language / proof assistant.
Although it is a proof assistant the only assistance it provides is checking
the correctness of your proofs. It does not perform proof search or anything
else SMT proof assistant like.

\par

First we import proofs about equality, so I do not have to prove them.

\begin{code}

module Fields where

open import Agda.Builtin.FromNat
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Unit
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

\end{code}

The following code defines an object that takes an identity element and a binary operation.
The object contains proofs that the identity element actually is the identity element.

This formulation allows us to reuse this structure for addition and multiplication.

\begin{code}

record Identity {F : Set} (e : F) (op : F → F → F) : Set where
  field
    left-identity : ∀ (a : F) → op e a ≡ a
    right-identity : ∀ (a : F) → op a e ≡ a

\end{code}

Now I list the field axioms. Agda lets you use any non space unicode character to
build identifiers. Underscores turn the function into a prefix, infix, or suffix
operator. To fully apply the operator you should place an argument inside every
underscore. This allows for notation close to math.

\begin{code}

F\_ : {F : Set} -> F -> Set
F\ z = ∃ (λ x -> ¬ (x ≡ z))

record Field (F : Set) : Set where
  infixl 6 _+_
  infixl 7 _·_
  field
    0# : F
    _+_ : F → F → F
    +-assoc : ∀ (a b c : F) → a + (b + c) ≡ (a + b) + c
    +-0-identity : Identity 0# _+_
    -_ : F → F
    +-left-inverse : ∀ (a : F) -> (- a) + a ≡ 0#
    +-right-inverse : ∀ (a : F) -> a + (- a) ≡ 0#
    1# : F
    _·_ : F → F → F
    ·-comm : ∀ (a b : F) → a · b ≡ b · a
    ·-assoc : ∀ (a b c : F) → a · (b · c) ≡ (a · b) · c
    ·-1-identity : Identity 1# _·_
    _⁻¹ : F\ 0# → F
    ·-left-inverse : ∀ (a : F\ 0#) -> a ⁻¹ · proj₁ a ≡ 1#
    ·-right-inverse : ∀ (a : F\ 0#) -> proj₁ a · a ⁻¹ ≡ 1#
    +-·-dist : ∀ (a b c : F) → a · (b + c) ≡ (a · b) + (a · c)
    0≠1 : ¬ (0# ≡ 1#)

\end{code}

Now we begin working over the set F which is a field. We avoid name clashes from
using the same structures for both addition and multiplication.
After this we use a hack in agda to overload numeric literals. This defines numbers
in the same way seen in the book. Now when we see 0 it will desugar to 0\# and 3
will desugar to (1\# + 1\#) + 1\#.

\begin{AgdaAlign}
\begin{code}

module FieldTheorems {F : Set} (f : Field F) where
  open Field f
  open Identity +-0-identity
    renaming ( left-identity to +-left-identity ; right-identity to +-right-identity )
  open Identity ·-1-identity
    renaming ( left-identity to ·-left-identity ; right-identity to ·-right-identity )

  instance
    FieldNumber : Number F
    FieldNumber =
      record
      { Constraint = λ _ → ⊤
      ; fromNat = natToField }
      where
      natToField : ℕ → {{_ : ⊤}} → F
      natToField 0 = 0#
      natToField 1 = 1#
      natToField 2 = 1# + 1#
      natToField (suc (suc n)) = (natToField n + 1#) + 1#

\end{code}

The pattern x ≡⟨ x≡y ⟩ y≡z represents the transitivity of equality where you specify the
left value of the equality that is inside the brackets. You can chain them together to perform logical
reasoning. The function cong (congruence) takes a function and an equality and applies the
function to both sides of the equality. In agda you can make annoymous functions with a lambda.

\begin{code}

  infixl 6 _-_
  _-_ : F → F → F
  x - y = x + (- y)

  +-cancellation-equality : ∀ {x y : F} → x - y ≡ 0 → x ≡ y
  +-cancellation-equality {x} {y} x-y≡0 =
    x ≡⟨ sym (+-right-identity x) ⟩
    x + 0 ≡⟨ cong (λ t → x + t) (sym (+-left-inverse y)) ⟩
    x + ((- y) + y) ≡⟨ +-assoc x (- y) y ⟩
    (x - y) + y ≡⟨ cong (λ t → t + y) x-y≡0 ⟩
    0 + y ≡⟨ +-left-identity y ⟩
    y ∎

  +-double-inverse : ∀ (x : F) → - (- x) ≡ x
  +-double-inverse x =
    - (- x) ≡⟨ sym (+-right-identity (- (- x))) ⟩
    - (- x) + 0 ≡⟨ cong (λ t → - (- x) + t) (sym (+-left-inverse x)) ⟩
    - (- x) + ((- x) + x) ≡⟨ +-assoc (- (- x)) (- x) x ⟩
    - (- x) + (- x) + x ≡⟨ cong (λ t → t + x) (+-left-inverse (- x)) ⟩
    0 + x ≡⟨ +-left-identity x ⟩
    x ∎

  ·-right-zero : ∀ (x : F) → x · 0 ≡ 0
  ·-right-zero x =  idempotent→unit lemma
    where
    idempotent→unit : ∀ {a : F} → a + a ≡ a → a ≡ 0
    idempotent→unit {a} a+a≡a =
      a ≡⟨ sym (+-right-identity a) ⟩
      a + 0 ≡⟨ cong (λ t → a + t) (sym (+-right-inverse a)) ⟩
      a + (a + (- a)) ≡⟨ +-assoc a a (- a) ⟩
      a + a + (- a) ≡⟨ cong (λ t →  t + (- a))  a+a≡a ⟩
      a + (- a) ≡⟨ +-right-inverse a ⟩
      0 ∎
    lemma : x · 0 + x · 0 ≡ x · 0
    lemma =
      x · 0 + x · 0 ≡⟨ sym (+-·-dist x 0 0) ⟩
      x · (0 + 0) ≡⟨ cong (λ t → x · t) (+-left-identity 0) ⟩
      x · 0 ∎

  2-77-a :  ∀ (a b : F) → (- a) · b ≡ - (a · b)
  2-77-a a b = +-cancellation-equality lemma
    where
    lemma : ((- a) · b) + (- (- (a · b))) ≡ 0
    lemma =
      ((- a) · b) + (- (- (a · b))) ≡⟨ cong (λ t → ((- a) · b) + t) sub-lemma ⟩
      ((- a) · b) + (b · a) ≡⟨ cong (λ t → t + (b · a)) (·-comm (- a) b) ⟩
      (b · (- a)) + (b · a) ≡⟨ sym (+-·-dist b (- a) a) ⟩
      b · ((- a) + a) ≡⟨ cong (λ t → b · t) (+-left-inverse a) ⟩
      b · 0 ≡⟨ ·-right-zero b ⟩
      0 ∎
      where
      sub-lemma : - (- (a · b)) ≡ b · a
      sub-lemma =
        - (- (a · b)) ≡⟨ +-double-inverse (a · b) ⟩
        a · b ≡⟨ ·-comm a b ⟩
        b · a ∎

  2-76 : ∀ (a b : F) → a · (- b) ≡ - (a · b)
  2-76 a b =
    a · (- b) ≡⟨ ·-comm a (- b) ⟩
    (- b) · a ≡⟨ 2-77-a b a ⟩
    - (b · a) ≡⟨ cong (-_) (·-comm b a) ⟩
    - (a · b) ∎

  2-77-b : ∀ (a : F) → a · (- 1) ≡ - a
  2-77-b a =
    a · (- 1) ≡⟨ ·-comm a (- 1) ⟩
    (- 1) · a ≡⟨ 2-77-a 1 a ⟩
    - (1 · a) ≡⟨ cong (-_) (·-left-identity a) ⟩
    - a ∎

  2-85-a : 3 + 3 ≡ 6
  2-85-a =
    3 + ((1 + 1) + 1) ≡⟨ +-assoc 3 (1 + 1) 1 ⟩
    (3 + (1 + 1)) + 1 ≡⟨ cong (λ t → t + 1) (+-assoc 3 1 1) ⟩
    ((3 + 1) + 1) + 1 ∎

  2-88 : ∀ (x : F) → 2 · x ≡ x + x
  2-88 x =
    2 · x ≡⟨ ·-comm 2 x ⟩
    x · (1 + 1) ≡⟨ +-·-dist x 1 1 ⟩
    (x · 1) + (x · 1) ≡⟨ cong (λ t → t + (x · 1)) (·-right-identity x) ⟩
    x + (x · 1) ≡⟨ cong (λ t → x + t) (·-right-identity x) ⟩
    x + x ∎

  2-85-b : 3 · 2 ≡ 6
  2-85-b =
    3 · 2 ≡⟨ ·-comm 3 2 ⟩
    2 · 3 ≡⟨ 2-88 3 ⟩
    3 + 3 ≡⟨ 2-85-a ⟩
    6 ∎

  2-90-a : ∀ (a b c : F) → a · (b - c) ≡ a · b - a · c
  2-90-a a b c =
    a · (b + (- c)) ≡⟨ +-·-dist a b (- c) ⟩
    (a · b) + (a · (- c)) ≡⟨ cong (λ t → (a · b) + t) (2-76 a c) ⟩
    (a · b) - (a · c) ∎

  2-90-b : ∀ (a b : F) → - (a - b) ≡ b - a
  2-90-b a b = sym (+-cancellation-equality lemma)
    where
    lemma : (b - a) - (- (a - b)) ≡ 0
    lemma =
      (b - a) + (- (- (a - b))) ≡⟨ cong (λ t → (b - a) + t) (+-double-inverse (a - b)) ⟩
      (b + (- a)) + (a + (- b)) ≡⟨ sym (+-assoc b (- a) (a + (- b))) ⟩
      (b + ((- a) + (a + (- b)))) ≡⟨ cong (λ t → b + t) (remove-a (- b)) ⟩
      b + (- b) ≡⟨ +-right-inverse b ⟩
      0 ∎
      where
      remove-a : ∀ (x : F) → (- a) + (a + x) ≡ x
      remove-a x =
        (- a) + (a + x) ≡⟨ +-assoc (- a) a x ⟩
        ((- a) + a) + x ≡⟨ cong (λ t → t + x) (+-left-inverse a) ⟩
        0 + x ≡⟨ +-left-identity x ⟩
        x ∎

  F\0 : Set
  F\0 = F\ 0#

  infixl 7 _/_
  _/_ : F → F\0 → F
  a / b = a · (b ⁻¹)

  ·-cancellation-equality : ∀ {x : F} {y : F\0} → x / y ≡ 1 → x ≡ proj₁ y
  ·-cancellation-equality {x} {y\0@(y , _)} x/y≡1 =
    x ≡⟨ sym (·-right-identity x) ⟩
    x · 1 ≡⟨ cong (λ t → x · t) (sym (·-left-inverse y\0)) ⟩
    x · (y\0 ⁻¹ · y) ≡⟨ ·-assoc x (y\0 ⁻¹) y ⟩
    (x · y\0 ⁻¹) · y ≡⟨ cong (λ t → t · y) x/y≡1 ⟩
    1 · y ≡⟨ ·-left-identity y ⟩
    y ∎

  ·-double-inverse : ∀ (x : F\0) → (x ⁻¹) ⁻¹ ≡ proj₁ x
  ·-double-inverse x =
    (x ⁻¹) ⁻¹ ≡⟨ sym (·-right-identity ((x ⁻¹) ⁻¹)) ⟩
    (x ⁻¹) ⁻¹ · 1 ≡⟨ cong (λ t → (x ⁻¹) ⁻¹ · t) (sym (·-left-inverse x)) ⟩
    (x ⁻¹) ⁻¹ · (x ⁻¹ · x) ≡⟨ ·-assoc ((x ⁻¹) ⁻¹) (x ⁻¹) x ⟩
    ((x ⁻¹) ⁻¹ · x ⁻¹) · x ≡⟨ cong (λ t → t · x) (·-left-inverse (x ⁻¹)) ⟩
    1 · x ≡⟨ ·-left-identity x ⟩
    x ∎

  -- ·-inverse-dist : ∀ (a b : F) → (a · b) ⁻¹ ≡ a ⁻¹ · b ⁻¹
  -- ·-inverse-dist a b =  sym (·-cancellation-equality lemma)
  --   where
  --   lemma : (a ⁻¹ · b ⁻¹) / ((a · b) ⁻¹) ≡ 1
  --   lemma =
  --     (a ⁻¹ · b ⁻¹) · (((a · b) ⁻¹) ⁻¹) ≡⟨ cong (λ t → (a ⁻¹ · b ⁻¹) · t) (·-double-inverse (a · b)) ⟩
  --     (a ⁻¹ · b ⁻¹) · (a · b) ≡⟨ ·-assoc (a ⁻¹ · b ⁻¹) a b ⟩
  --     ((a ⁻¹ · b ⁻¹) · a) · b ≡⟨ cong (λ t →  t · b) ( sub-lemma (b ⁻¹)) ⟩
  --     b ⁻¹ · b ≡⟨  ·-left-inverse b ⟩
  --     1 ∎
  --     where
  --     sub-lemma : ∀ (x : F) → (a ⁻¹ · x) · a ≡ x
  --     sub-lemma x =
  --       (a ⁻¹ · x) · a ≡⟨ cong (λ t →  t · a) (·-comm (a ⁻¹) x) ⟩
  --       (x · a ⁻¹) · a ≡⟨ sym (·-assoc x (a ⁻¹) a) ⟩
  --       x · (a ⁻¹ · a) ≡⟨ cong (λ t →  x · t) (·-left-inverse a) ⟩
  --       x · 1 ≡⟨ ·-right-identity x ⟩
  --       x ∎

  -- 2-93-b : ∀ (a b d : F) → (d · a) / (d · b) ≡ a / b
  -- 2-93-b a b d =
  --   (d · a) · (d · b) ⁻¹ ≡⟨ cong (λ t → (d · a) · t)  (·-inverse-dist d b) ⟩
  --   (d · a) · (d ⁻¹ · b ⁻¹) ≡⟨ cong (λ t → t · (d ⁻¹ · b ⁻¹)) (·-comm d a) ⟩
  --   (a · d) · (d ⁻¹ · b ⁻¹) ≡⟨ sym (·-assoc a d (d ⁻¹ · b ⁻¹)) ⟩
  --   a · (d · (d ⁻¹ · b ⁻¹)) ≡⟨ cong (λ t → a · t) (remove-d (b ⁻¹)) ⟩
  --   a / b ∎
  --   where
  --   remove-d : ∀ (x : F) → d · (d ⁻¹ · x) ≡ x
  --   remove-d x =
  --     d · (d ⁻¹ · x) ≡⟨ ·-assoc d (d ⁻¹) x ⟩
  --     (d · d ⁻¹) · x ≡⟨ cong (λ t → t · x) (·-right-inverse d) ⟩
  --     1 · x ≡⟨ ·-left-identity x ⟩
  --     x ∎

  -- 2-93-e : ∀ (a b c d : F) → (a · d + b · c) / (b · d) ≡ a / b + c / d
  -- 2-93-e a b c d =
  --   (a · d + b · c) · (b · d) ⁻¹ ≡⟨ cong (λ t → (a · d + b · c) · t) (·-inverse-dist b d) ⟩
  --   (a · d + b · c) · (b ⁻¹ · d ⁻¹) ≡⟨ ·-comm (a · d + b · c) (b ⁻¹ · d ⁻¹) ⟩
  --   (b ⁻¹ · d ⁻¹) · (a · d + b · c) ≡⟨ +-·-dist (b ⁻¹ · d ⁻¹) (a · d) (b · c) ⟩
  --   (b ⁻¹ · d ⁻¹) · (a · d) + (b ⁻¹ · d ⁻¹) · (b · c) ≡⟨ cong (λ t → t + (b ⁻¹ · d ⁻¹) · (b · c)) lemma-a/b ⟩
  --   a / b + (b ⁻¹ · d ⁻¹) · (b · c) ≡⟨ cong (λ t → a / b + t) lemma-c/d ⟩
  --   a / b + c / d ∎
  --   where
  --   lemma-a/b : (b ⁻¹ · d ⁻¹) · (a · d) ≡ a / b
  --   lemma-a/b =
  --     (b ⁻¹ · d ⁻¹) · (a · d) ≡⟨ ·-comm (b ⁻¹ · d ⁻¹) (a · d) ⟩
  --     (a · d) · (b ⁻¹ · d ⁻¹) ≡⟨ sym (·-assoc a d (b ⁻¹ · d ⁻¹)) ⟩
  --     a · (d · (b ⁻¹ · d ⁻¹)) ≡⟨ cong (λ t → a · t) (sub-lemma-a/b (b ⁻¹)) ⟩
  --     a / b ∎
  --     where
  --     sub-lemma-a/b : ∀ (x : F) → d · (x · d ⁻¹) ≡ x
  --     sub-lemma-a/b x =
  --       d · (x · d ⁻¹) ≡⟨ cong (λ t → d · t) (·-comm x (d ⁻¹)) ⟩
  --       d · (d ⁻¹ · x) ≡⟨ ·-assoc d (d ⁻¹) x ⟩
  --       (d · d ⁻¹) · x ≡⟨ cong (λ t → t · x) (·-right-inverse d) ⟩
  --       1 · x ≡⟨ ·-left-identity x ⟩
  --       x ∎
  --   lemma-c/d : (b ⁻¹ · d ⁻¹) · (b · c) ≡ c / d
  --   lemma-c/d =
  --     (b ⁻¹ · d ⁻¹) · (b · c) ≡⟨ ·-comm (b ⁻¹ · d ⁻¹) (b · c)⟩
  --     (b · c) · (b ⁻¹ · d ⁻¹) ≡⟨ cong (λ t → t · (b ⁻¹ · d ⁻¹)) (·-comm b c) ⟩
  --     (c · b) · (b ⁻¹ · d ⁻¹) ≡⟨ sym (·-assoc c b (b ⁻¹ · d ⁻¹)) ⟩
  --     c · (b · (b ⁻¹ · d ⁻¹)) ≡⟨ cong (λ t → c · t) (sub-lemma-c/d (d ⁻¹)) ⟩
  --     c / d ∎
  --     where
  --     sub-lemma-c/d : ∀ (x : F) → b · (b ⁻¹ · x) ≡ x
  --     sub-lemma-c/d x =
  --       b · (b ⁻¹ · x) ≡⟨ ·-assoc b (b ⁻¹) x ⟩
  --       (b · b ⁻¹) · x ≡⟨ cong (λ t → t · x) (·-right-inverse b) ⟩
  --       1 · x ≡⟨ ·-left-identity x ⟩
  --       x ∎

  -- _² : F → F
  -- x ² = x · x

  -- 2-94-a : ∀ (a b : F) → (a + b) ² ≡ a ² + 2 · a · b + b ²
  -- 2-94-a a b =
  --   (a + b) · (a + b) ≡⟨ +-·-dist (a + b) a b ⟩
  --   ((a + b) · a) + ((a + b) · b) ≡⟨ cong (λ t → t + ((a + b) · b)) lemma-a ⟩
  --   (a ² + a · b) + ((a + b) · b) ≡⟨ cong (λ t → (a ² + a · b) + t) lemma-b ⟩
  --   (a ² + a · b) + (a · b + b ²) ≡⟨ sym (+-assoc (a ²) (a · b) (a · b + b ²)) ⟩
  --   a ² + ((a · b) + (a · b + b ²)) ≡⟨ cong (λ t → a ² + t) lemma-c ⟩
  --   a ² + (2 · a · b + b ²) ≡⟨ +-assoc (a ²) (2 · a · b) (b ²) ⟩
  --   a ² + 2 · a · b + b ² ∎
  --   where
  --   lemma-a : (a + b) · a ≡ a ² + a · b
  --   lemma-a =
  --     (a + b) · a ≡⟨ ·-comm (a + b) a ⟩
  --     a · (a + b) ≡⟨ +-·-dist a a b ⟩
  --     a ² + a · b ∎
  --   lemma-b : (a + b) · b ≡ a · b + b ²
  --   lemma-b =
  --     (a + b) · b ≡⟨ ·-comm (a + b) b ⟩
  --     b · (a + b) ≡⟨ +-·-dist b a b ⟩
  --     (b · a) + b ² ≡⟨ cong (λ t → t + b ²) (·-comm b a) ⟩
  --     a · b + b ² ∎
  --   lemma-c : (a · b) + (a · b + b ²) ≡ 2 · a · b + b ²
  --   lemma-c =
  --     (a · b) + (a · b + b ²) ≡⟨ +-assoc (a · b) (a · b) (b ²) ⟩
  --     (a · b + a · b) + b ² ≡⟨ cong (λ t → t + b ²) sub-lemma-c ⟩
  --     2 · a · b + b ² ∎
  --     where
  --     sub-lemma-c : (a · b + a · b) ≡ 2 · a · b
  --     sub-lemma-c =
  --       a · b + a · b ≡⟨ sym (2-88 (a · b)) ⟩
  --       2 · (a · b) ≡⟨ ·-assoc 2 a b ⟩
  --       2 · a · b ∎

  -- 2-94-c : ∀ (a b : F) → (a - b) · (a + b) ≡ a ² - b ²
  -- 2-94-c a b =
  --   (a - b) · (a + b) ≡⟨ +-·-dist (a - b) a b ⟩
  --   (a - b) · a + (a - b) · b ≡⟨ cong (λ t → t + (a - b) · b) lemma-a ⟩
  --   a ² - a · b + (a - b) · b ≡⟨ cong (λ t → a ² - a · b + t) lemma-b ⟩
  --   a ² + (- (a · b)) + (a · b - b ²) ≡⟨ sym (+-assoc (a ²) (- (a · b)) (a · b - b ²) ) ⟩
  --   a ² + ((- (a · b)) + (a · b - b ²)) ≡⟨ cong (λ t → a ² + t) lemma-cancel ⟩
  --   a ² - b ² ∎
  --   where
  --   lemma-a : (a - b) · a ≡ a ² - a · b
  --   lemma-a =
  --     (a - b) · a ≡⟨ ·-comm (a - b) a ⟩
  --     a · (a + (- b)) ≡⟨ +-·-dist a a (- b) ⟩
  --     a ² + a · (- b) ≡⟨ cong (λ t → a ² + t) (2-76 a b) ⟩
  --     a ² - a · b ∎
  --   lemma-b : (a - b) · b ≡ a · b - b ²
  --   lemma-b =
  --     (a - b) · b ≡⟨ ·-comm (a - b) b ⟩
  --     b · (a + (- b)) ≡⟨ +-·-dist b a (- b) ⟩
  --     b · a + b · (- b) ≡⟨ cong (λ t → b · a + t) (2-76 b b) ⟩
  --     b · a + (- (b ²)) ≡⟨ cong (λ t → t + (- (b ²))) (·-comm b a)⟩
  --     a · b - b ² ∎
  --   lemma-cancel : (- (a · b)) + (a · b - b ²) ≡ - (b ² )
  --   lemma-cancel =
  --     (- (a · b)) + (a · b - b ²) ≡⟨ +-assoc (- (a · b)) (a · b) (- (b ²)) ⟩
  --     ((- (a · b)) + a · b) - b ² ≡⟨ cong (λ t → t - b ²) (+-left-inverse (a · b))⟩
  --     0 + (- (b ²)) ≡⟨ +-left-identity (- (b ²)) ⟩
  --     - (b ²) ∎

\end{code}
\end{AgdaAlign}
\end{document}
