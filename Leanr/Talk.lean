import Mathlib

variable {α : Type}

inductive MyList (α : Type) : Type where
  | nil : MyList α
  | cons (head : α) (tail : MyList α) : MyList α
  deriving Repr, BEq


#eval MyList.cons 2 .nil

@[simp]
def MyList.length {α : Type} : MyList α → ℕ
  | .nil => 0
  | .cons _ tail => 1 + tail.length


#eval (MyList.cons 2 (MyList.cons 3 .nil)).length


@[simp]
def MyList.append : MyList α → MyList α → MyList α :=
  fun x y => match x, y with
  | .nil, ys => ys
  | .cons x xs, ys => .cons x (append xs ys)

@[simp]
theorem MyList.append_length {α : Type} (xs ys : MyList α) :
    (MyList.append xs ys).length = xs.length + ys.length := by
  induction xs with
  | nil => simp
  | cons head tail ih =>
    calc
          ((cons head tail).append ys).length
        = (cons head (tail.append ys)).length := rfl
      _ = 1 + (tail.append ys).length := rfl
      _ = 1 + (tail.length + ys.length) := by rw [ih]
      _ = (1 + tail.length) + ys.length := by rw [Nat.add_assoc]
      _ = (cons head tail).length + ys.length := rfl

#print MyList.append_length

structure ExactLengthList (n : Nat) where
  list : MyList ℕ
  length_eq : list.length = n := by simp

def ExactLengthList.nil : ExactLengthList 0 := { list := .nil }


#print MyList.append_length

def ExactLengthList.append {n m : Nat}
  (xs : ExactLengthList n) (ys : ExactLengthList m) :
    ExactLengthList (n + m) :=
  {
    list := MyList.append xs.list ys.list
    length_eq := by simp [xs.length_eq, ys.length_eq]
  }


def square (n : ℕ) : ℕ := n * n


def is_square (n : ℕ) : Prop := ∃ m, n = square m

theorem sixteen_is_square : is_square 16 := by use 4; simp [square]
