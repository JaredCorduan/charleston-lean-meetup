/-

== Inductive Types ==

inductive Foo where
  | constructor₁ : ... → Foo
  | constructor₂ : ... → Foo
  ...
  | constructorₙ : ... → Foo

-/


-- Example: Lists

inductive L (α : Sort u) where
  | nil : L α
  | cons : α → L α → L α

example : L Nat := L.cons 17 (L.cons 42 L.nil)


def length (xs : L α) : Nat :=
  match xs with
  | L.nil => 0
  | L.cons _ xs => 1 + length xs


def iter (xs : L α) (b : β) (step : α → β → β) : β :=
  match xs with
  | L.nil => b
  | L.cons x xs => step x (iter xs b step)


def length₂ (xs : L α) : Nat :=
  iter xs 0 (λ _ n => n+1)

#print L.rec
#print L.recOn

--def length₃ (xs : L α) : Nat :=
--  L.recOn xs 0 (λ x => λ xs => λ acc => 1+acc)





-- Example: Optional / Maybe

inductive Opt α where
  | nothing : Opt α
  | just : α → Opt α


def head : L α → Opt α
  | L.nil => Opt.nothing
  | L.cons x _ => Opt.just x



-- Example: Natural Numbers 0, 1, 2, …

inductive N where
  | zero : N
  | succ : N → N
  deriving Repr -- for #eval


def one := N.succ N.zero
def two := N.succ one
def three := N.succ two


#check @N.rec


def addN (m n : N) : N :=
  match n with
  | N.zero   => m
  | N.succ n => N.succ (addN m n)


#eval addN one two
example : addN one two = three := rfl


-- The Add typeclass lets us use the plus symbol
instance : Add N where
  add := addN


/-

GOALS for N:

1) (x + y) + z = x + (y + z)

2) x + y = y + x

3) m + n = p + n → m = p

Tools:

1) rfl
2) structural recursion
3) rewriting (rw tactic)
4) congrArg: IF a = b THEN f(a) = f(b)

-/


-- Two easy theorems:

theorem add_zero (m : N) : m + N.zero = m := rfl

-- Notice this fails to work:
--theorem zero_add (m : N) : N.zero + m = m := rfl

#print add_zero


theorem add_succ (m n : N) : m + (N.succ n) = N.succ (m + n) := rfl



-- DETOUR: the magic of RFL
-- Note we haven't seen Indexed Families yet

inductive IsTheSameAs {α : Sort u} (a : α) : α → Prop where
  | funnel_of_truth : IsTheSameAs a a

theorem one_and_one_is_two : IsTheSameAs (one + one) two := IsTheSameAs.funnel_of_truth

infix:50 " 🍕 " => IsTheSameAs
theorem one_and_one_is_still_two : one + one 🍕 two := IsTheSameAs.funnel_of_truth



-- Back to arithmetic!


theorem succ_left (m n : N) : N.succ m + n = N.succ (m + n) :=
  match n with
  | N.zero => rfl
  | N.succ x => by rw [add_succ, add_succ, succ_left]
  --| N.succ x => congrArg N.succ (succ_left m x)

#print congrArg



theorem zero_add (n : N) : N.zero + n = n :=
  match n with
  | N.zero => rfl
  | N.succ x => congrArg N.succ (zero_add x)

#print zero_add



-- here is a proof using two things I don't use:
-- recOn and calc

theorem zero_add_ALT (n : N) : N.zero + n = n :=
  N.recOn (motive := fun x => N.zero + x = x)
   n
   (show N.zero + N.zero = N.zero from rfl)
   (fun (n : N) (ih : N.zero + n = n) =>
    show N.zero + N.succ n = N.succ n from
    calc N.zero + N.succ n
      _ = N.succ (N.zero + n) := rfl
      _ = N.succ n            := by rw [ih])



theorem add_comm (m n : N) : m + n = n + m :=
  match n with
  | N.zero => by rw [zero_add]; rfl
  | N.succ x =>
    have h : N.succ (m + x) = N.succ (x + m) := congrArg N.succ (add_comm m x)
    by rw [← succ_left x m] at h; exact h
  --N.succ x => by rw [succ_left, add_succ, add_comm]


theorem add_assoc (m n p : N) : m + (n + p) = (m + n) + p :=
  match p with
  | N.zero => rfl
  | N.succ q => -- show  m + (n + (q+1)) = (m + n) + (q + 1)
      have h1 : m + (n + q) = m + n + q := add_assoc m n q
      have h2 : N.succ (m + (n + q)) = N.succ (m + n + q) := congrArg N.succ h1
      have h3 : m + N.succ (n + q) = m + n + N.succ q := h2
      have h4 : m + (n + N.succ q) = m + n + N.succ q := h3
      h4
  --| N.succ q => congrArg N.succ (add_assoc m n q)


theorem succ_lemma (m n : N) : N.succ (m + n) = N.succ m + n :=
  match n with
  | N.zero => rfl
  | N.succ p => by rw [succ_left]
  --| N.succ p => congrArg N.succ (succ_lemma m p)

def pred (m : N) : N :=
  match m with
  | N.zero => N.zero
  | N.succ n => n

theorem succ_inj {m n : N} (h : N.succ m = N.succ n) : m = n := congrArg pred h

theorem add_cancel_right {m n p : N} (h : m + n = p + n) : m = p :=
  match n with
  | N.zero => h
  | N.succ _ => add_cancel_right (succ_inj h)

theorem add_cancel_left {m n p : N} (h : m + n = m + p) : n = p :=
  have h1 : n + m = p + m := by rw [add_comm, add_comm m p] at h; exact h
  add_cancel_right h1




/-

🎉 GOALS COMPLETE 🎉

What could we do next?

* Multiplication
* Arithmetic facts
* Binary notation
* Integers

-/


-- Multiplication

def mult (m n : N) : N :=
  match n with
  | N.zero   => N.zero
  | N.succ n => (mult m n) + m

instance : Mul N where
  mul := mult

theorem mult_assoc (m n p : N) : (m * n) * p = m * (n * p) := sorry
theorem mult_comm (m n : N) : m * n = n * m := sorry
theorem mult_distr_add (m n p: N) : m * (n + p) = (m * n) + (m * p) := sorry




-- Binary representation of numbers

inductive Bin where
  | ε : Bin
  | O : Bin → Bin
  | I : Bin → Bin


open Bin

notation:50 x "◯" => Bin.O x
notation:50 x "Ⅰ" => Bin.I x


def eight := ε Ⅰ ◯ ◯ ◯



def incr (b : Bin) : Bin :=
  match b with
  | ε   => ε Ⅰ
  | ε Ⅰ => ε Ⅰ ◯
  | b ◯ => b Ⅰ
  | b Ⅰ => (incr b) ◯

def toN (b : Bin) : N :=
  match b with
  | ε     => N.zero
  | b' ◯ => toN b' + toN b'
  | b' Ⅰ  => toN b' + toN b' + N.succ N.zero

def toB (n : N) : Bin :=
  match n with
  | N.zero => ε ◯
  | N.succ n => incr (toB n)

-- Prove if true, find counterexample otherwise

theorem incr_succ (b : Bin) : toN (incr b) = N.succ (toN b) := sorry

theorem to_from (b : Bin) : toB (toN b) = b := sorry

theorem from_to (n : N) : toN (toB n) = n := sorry




-- Integers
--
-- we represent x ∈ ℤ by (x, y)
-- where (x, y) is thought of as x - y

inductive Z where
  | mk : N → N → Z

-- (a - b) = (c - d) IFF a + d = c + b
def Zequiv (x y : Z) : Prop :=
  match (x, y) with
  | (Z.mk a b, Z.mk c d) => a + d = c + b

infix:50 " ~ " => Zequiv

-- Zequiv is an Equivalenc Relation
--
-- Reflexive:  x ~ x
-- Symetric:   IF x ~ y THEN y ~ x
-- Transitive: IF x ~ y AND y ~ z THEN x ~ z

theorem ze_refl (x : Z) : x ~ x := rfl

theorem ze_symm : ∀ {x y : Z}, x ~ y → y ~ x
  | Z.mk a b, Z.mk c d => λ h =>
    have h': c + b = a + d := by rw [h]
    h'

theorem add_eqns : ∀ {a b c d : N}, a = b → c = d → a + c = b + d :=
  λ h1 => λ h2 => by rw [h1, h2]

theorem ze_trans : ∀ {x y z : Z}, x ~ y → y ~ z → x ~ z
  | Z.mk a b, Z.mk c d, Z.mk e f =>
    λ hxy => λ hyz =>
      have h: (a + d) + (c + f) = (c + b) + (e + d) := add_eqns hxy hyz

      -- Plan:
      --   use commutivity and associativity to move c and d so
      --   where they can be canceled

      -- Move d + c to the far right on the RHS
      have hr: (a + f) + (d + c) = (c + b) + (e + d) := by
        rw [ add_comm c f
           , ← add_assoc
           , add_assoc d f c
           , add_comm d f
           , ← add_assoc f d c
           , add_assoc
           ] at h;
        exact h

      -- Move d + c to the far right on the LHS
      have hl: (a + f) + (d + c) = (e + b) + (d + c) := by
        rw [ add_comm c b
           , ← add_assoc b c
           , add_assoc c e d
           , add_comm c e
           , ← add_assoc e c d
           , add_assoc b e
           , add_comm c d
           , add_comm b e
           ] at hr; exact hr

      add_cancel_right hl


theorem ze_equivalence : Equivalence Zequiv :=
  { refl := ze_refl, symm := ze_symm, trans := ze_trans }

instance : Setoid Z where
  r     := Zequiv
  iseqv := ze_equivalence

def neg_two := Quotient.mk' (Z.mk N.zero two)
#check neg_two
