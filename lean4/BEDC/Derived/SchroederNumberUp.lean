import BEDC.Algebra.FiniteFold
import BEDC.Derived.CatalanConvolutionUp
import BEDC.Derived.IntUp
import BEDC.Derived.MotzkinPathUp

namespace BEDC.Derived.SchroederNumberUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp (natToUnary natToUnary_length natToUnary_unary)

def listLen {A : Type u} : List A -> Nat
  | [] => 0
  | _ :: xs => Nat.succ (listLen xs)

def listNthNat : List Nat -> Nat -> Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, Nat.succ n => listNthNat xs n

def smallSchroederInternalConvolutionFromPrefix
    (pref : List Nat) : Nat -> Nat -> Nat -> Nat
  | 0, _index, _top => 0
  | Nat.succ fuel, index, top =>
      listNthNat pref index * listNthNat pref (top - index) +
        smallSchroederInternalConvolutionFromPrefix pref fuel (Nat.succ index) top

def smallSchroederInternalConvolutionPrefix (pref : List Nat) : Nat -> Nat
  | 0 => 0
  | Nat.succ inner =>
      smallSchroederInternalConvolutionFromPrefix pref inner 1 (Nat.succ inner)

def smallSchroederNext (pref : List Nat) : Nat -> Nat
  | 0 => 1
  | Nat.succ n =>
      3 * listNthNat pref (Nat.succ n) +
        2 * smallSchroederInternalConvolutionPrefix pref (Nat.succ n)

def smallSchroederPrefix : Nat -> List Nat
  | 0 => [1]
  | Nat.succ n =>
      let pref := smallSchroederPrefix n
      pref ++ [smallSchroederNext pref n]

def smallSchroederNumber (n : Nat) : Nat :=
  listNthNat (smallSchroederPrefix n) n

def largeSchroederNumber : Nat -> Nat
  | 0 => 1
  | Nat.succ n => 2 * smallSchroederNumber (Nat.succ n)

def smallSchroederInternalConvolutionFrom : Nat -> Nat -> Nat -> Nat
  | 0, _index, _top => 0
  | Nat.succ fuel, index, top =>
      smallSchroederNumber index * smallSchroederNumber (top - index) +
        smallSchroederInternalConvolutionFrom fuel (Nat.succ index) top

def smallSchroederInternalConvolution : Nat -> Nat
  | 0 => 0
  | Nat.succ inner =>
      smallSchroederInternalConvolutionFrom inner 1 (Nat.succ inner)

def largeSchroederConvolutionFrom : Nat -> Nat -> Nat -> Nat
  | 0, _index, _top => 0
  | Nat.succ fuel, index, top =>
      largeSchroederNumber index * largeSchroederNumber (top - index) +
        largeSchroederConvolutionFrom fuel (Nat.succ index) top

def largeSchroederConvolution (top : Nat) : Nat :=
  largeSchroederConvolutionFrom (Nat.succ top) 0 top

def largeSchroederNumberFn (n : BHist) : BHist :=
  natToUnary (largeSchroederNumber (bwordLength n))

def smallSchroederNumberFn (n : BHist) : BHist :=
  natToUnary (smallSchroederNumber (bwordLength n))

inductive SchroederStep : Type where
  | east : SchroederStep
  | north : SchroederStep
  | diag : SchroederStep

def schroederStepLength : List SchroederStep -> Nat
  | [] => 0
  | _ :: steps => Nat.succ (schroederStepLength steps)

inductive SchroederWalk : Nat -> Nat -> List SchroederStep -> Nat -> Nat -> Prop where
  | nil {x y : Nat} :
      SchroederWalk x y [] x y
  | east {x y finishX finishY : Nat} {tail : List SchroederStep} :
      SchroederWalk (Nat.succ x) y tail finishX finishY ->
        SchroederWalk x y (SchroederStep.east :: tail) finishX finishY
  | north {x y finishX finishY : Nat} {tail : List SchroederStep} :
      SchroederWalk x (Nat.succ y) tail finishX finishY ->
        SchroederWalk x y (SchroederStep.north :: tail) finishX finishY
  | diag {x y finishX finishY : Nat} {tail : List SchroederStep} :
      SchroederWalk (Nat.succ x) (Nat.succ y) tail finishX finishY ->
        SchroederWalk x y (SchroederStep.diag :: tail) finishX finishY

def LargeSchroederPath (n : Nat) (steps : List SchroederStep) : Prop :=
  SchroederWalk 0 0 steps n n

def LargeSchroederPathOfLength
    (n length : Nat) (steps : List SchroederStep) : Prop :=
  LargeSchroederPath n steps ∧ schroederStepLength steps = length

inductive SmallSchroederWalk :
    Bool -> Nat -> Nat -> List SchroederStep -> Nat -> Nat -> Prop where
  | nil {started : Bool} {x y : Nat} :
      SmallSchroederWalk started x y [] x y
  | east {started : Bool} {x y finishX finishY : Nat}
      {tail : List SchroederStep} :
      SmallSchroederWalk true (Nat.succ x) y tail finishX finishY ->
        SmallSchroederWalk started x y
          (SchroederStep.east :: tail) finishX finishY
  | north {started : Bool} {x y finishX finishY : Nat}
      {tail : List SchroederStep} :
      SmallSchroederWalk true x (Nat.succ y) tail finishX finishY ->
        SmallSchroederWalk started x y
          (SchroederStep.north :: tail) finishX finishY
  | diag {x y finishX finishY : Nat} {tail : List SchroederStep} :
      SmallSchroederWalk true (Nat.succ x) (Nat.succ y)
        tail finishX finishY ->
        SmallSchroederWalk true x y
          (SchroederStep.diag :: tail) finishX finishY

def SmallSchroederPath (n : Nat) (steps : List SchroederStep) : Prop :=
  SmallSchroederWalk false 0 0 steps n n

def catalanNumber : Nat -> Nat :=
  BEDC.Derived.CatalanConvolutionUp.catalanNumber

def motzkinNumber : Nat -> Nat :=
  BEDC.Derived.MotzkinPathUp.motzkinNumber

theorem listLen_append_singleton {A : Type u} (xs : List A) (x : A) :
    listLen (xs ++ [x]) = Nat.succ (listLen xs) := by
  induction xs with
  | nil =>
      rfl
  | cons _ tail ih =>
      exact congrArg Nat.succ ih

theorem listNthNat_append_at_listLen (xs : List Nat) (x : Nat) :
    listNthNat (xs ++ [x]) (listLen xs) = x := by
  induction xs with
  | nil =>
      rfl
  | cons _ tail ih =>
      exact ih

theorem listNthNat_append_at_succ_of_listLen (xs : List Nat) (x n : Nat)
    (h : listLen xs = Nat.succ n) :
    listNthNat (xs ++ [x]) (Nat.succ n) = x := by
  exact Eq.ndrec (motive := fun k => listNthNat (xs ++ [x]) k = x)
    (listNthNat_append_at_listLen xs x) h

theorem smallSchroederPrefix_listLen (n : Nat) :
    listLen (smallSchroederPrefix n) = Nat.succ n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      exact Eq.trans
        (listLen_append_singleton (smallSchroederPrefix n)
          (smallSchroederNext (smallSchroederPrefix n) n))
        (congrArg Nat.succ ih)

theorem smallSchroeder_zero :
    smallSchroederNumber 0 = 1 := by
  rfl

theorem smallSchroeder_one :
    smallSchroederNumber 1 = 1 := by
  rfl

theorem largeSchroeder_zero :
    largeSchroederNumber 0 = 1 := by
  rfl

theorem largeSchroeder_one :
    largeSchroederNumber 1 = 2 := by
  rfl

theorem smallSchroeder_succ_prefix_recursion (n : Nat) :
    smallSchroederNumber (Nat.succ n) =
      smallSchroederNext (smallSchroederPrefix n) n := by
  exact listNthNat_append_at_succ_of_listLen
    (smallSchroederPrefix n)
    (smallSchroederNext (smallSchroederPrefix n) n)
    n
    (smallSchroederPrefix_listLen n)

private theorem listNthNat_append_left_of_lt_listLen :
    ∀ xs ys : List Nat, ∀ i : Nat,
      i < listLen xs -> listNthNat (xs ++ ys) i = listNthNat xs i
  | [], _ys, _i, h => by
      cases h
  | _x :: _xs, _ys, 0, _h => by
      rfl
  | _x :: xs, ys, Nat.succ i, h => by
      exact listNthNat_append_left_of_lt_listLen xs ys i
        (Nat.lt_of_succ_lt_succ h)

private theorem nat_le_add_right_self (i extra : Nat) :
    i <= i + extra := by
  induction extra with
  | zero =>
      rw [Nat.add_zero]
      exact Nat.le_refl i
  | succ extra ih =>
      rw [Nat.add_succ]
      exact Nat.le_trans ih (Nat.le_succ (i + extra))

private theorem lt_succ_add_right (i extra : Nat) :
    i < Nat.succ (i + extra) := by
  exact Nat.succ_le_succ (nat_le_add_right_self i extra)

private theorem le_to_add_tail {i n : Nat} :
    i <= n -> ∃ extra : Nat, n = i + extra := by
  intro h
  obtain ⟨extra, hEq⟩ := Nat.le.dest h
  exact ⟨extra, hEq.symm⟩

theorem smallSchroederPrefix_nth_stable_add (i extra : Nat) :
    listNthNat (smallSchroederPrefix (i + extra)) i =
      smallSchroederNumber i := by
  induction extra with
  | zero =>
      rw [Nat.add_zero]
      rfl
  | succ extra ih =>
      rw [Nat.add_succ]
      change
        listNthNat
            (smallSchroederPrefix (i + extra) ++
              [smallSchroederNext
                (smallSchroederPrefix (i + extra)) (i + extra)])
            i =
          smallSchroederNumber i
      rw [listNthNat_append_left_of_lt_listLen
        (smallSchroederPrefix (i + extra))
        [smallSchroederNext (smallSchroederPrefix (i + extra)) (i + extra)]
        i]
      · exact ih
      · rw [smallSchroederPrefix_listLen]
        exact lt_succ_add_right i extra

theorem smallSchroederPrefix_nth_stable_of_le {i n : Nat} (h : i <= n) :
    listNthNat (smallSchroederPrefix n) i = smallSchroederNumber i := by
  obtain ⟨extra, hEq⟩ := le_to_add_tail h
  rw [hEq]
  exact smallSchroederPrefix_nth_stable_add i extra

private theorem smallSchroederInternalConvolutionFromPrefix_eq_numberFrom :
    ∀ fuel index top bound : Nat,
      top <= bound ->
      index + fuel = top ->
        smallSchroederInternalConvolutionFromPrefix
            (smallSchroederPrefix bound) fuel index top =
          smallSchroederInternalConvolutionFrom fuel index top
  | 0, _index, _top, _bound, _topLeBound, _sumBound => by
      rfl
  | Nat.succ fuel, index, top, bound, topLeBound, sumBound => by
      change
        listNthNat (smallSchroederPrefix bound) index *
            listNthNat (smallSchroederPrefix bound) (top - index) +
            smallSchroederInternalConvolutionFromPrefix
              (smallSchroederPrefix bound) fuel (Nat.succ index) top =
          smallSchroederNumber index * smallSchroederNumber (top - index) +
            smallSchroederInternalConvolutionFrom fuel (Nat.succ index) top
      have indexLe : index <= top := by
        have raw : index <= index + Nat.succ fuel :=
          nat_le_add_right_self index (Nat.succ fuel)
        rw [sumBound] at raw
        exact raw
      have indexLeBound : index <= bound :=
        Nat.le_trans indexLe topLeBound
      have tailLe : top - index <= top :=
        Nat.sub_le top index
      have tailLeBound : top - index <= bound :=
        Nat.le_trans tailLe topLeBound
      rw [smallSchroederPrefix_nth_stable_of_le indexLeBound]
      rw [smallSchroederPrefix_nth_stable_of_le tailLeBound]
      have nextBound : Nat.succ index + fuel = top := by
        rw [Nat.succ_add]
        exact sumBound
      rw [smallSchroederInternalConvolutionFromPrefix_eq_numberFrom fuel
        (Nat.succ index) top bound topLeBound nextBound]

theorem smallSchroederInternalConvolution_eq_recurrence (n : Nat) :
    smallSchroederInternalConvolutionPrefix (smallSchroederPrefix n) n =
      smallSchroederInternalConvolution n := by
  cases n with
  | zero =>
      rfl
  | succ inner =>
      exact smallSchroederInternalConvolutionFromPrefix_eq_numberFrom
        inner 1 (Nat.succ inner) (Nat.succ inner)
        (Nat.le_refl (Nat.succ inner))
        (Nat.one_add inner)

theorem smallSchroeder_succ_succ_recursion (n : Nat) :
    smallSchroederNumber (Nat.succ (Nat.succ n)) =
      3 * smallSchroederNumber (Nat.succ n) +
        2 * smallSchroederInternalConvolution (Nat.succ n) := by
  rw [smallSchroeder_succ_prefix_recursion (Nat.succ n)]
  change
    3 * listNthNat (smallSchroederPrefix (Nat.succ n)) (Nat.succ n) +
        2 * smallSchroederInternalConvolutionPrefix
          (smallSchroederPrefix (Nat.succ n)) (Nat.succ n) =
      3 * smallSchroederNumber (Nat.succ n) +
        2 * smallSchroederInternalConvolution (Nat.succ n)
  rw [smallSchroederPrefix_nth_stable_of_le (Nat.le_refl (Nat.succ n))]
  rw [smallSchroederInternalConvolution_eq_recurrence (Nat.succ n)]

theorem smallSchroeder_succ_succ_recursion_strong (n : Nat) :
    smallSchroederNumber (Nat.succ (Nat.succ n)) =
      3 * smallSchroederNumber (Nat.succ n) +
        2 * smallSchroederInternalConvolution (Nat.succ n) := by
  exact Nat.strongRecOn n
    (motive := fun k =>
      smallSchroederNumber (Nat.succ (Nat.succ k)) =
        3 * smallSchroederNumber (Nat.succ k) +
          2 * smallSchroederInternalConvolution (Nat.succ k))
    (fun k _ih => smallSchroeder_succ_succ_recursion k)

theorem largeSchroeder_succ_eq_two_small (n : Nat) :
    largeSchroederNumber (Nat.succ n) =
      2 * smallSchroederNumber (Nat.succ n) := by
  rfl

theorem largeSchroeder_positive_eq_two_small (n : Nat) (h : 0 < n) :
    largeSchroederNumber n = 2 * smallSchroederNumber n := by
  cases n with
  | zero =>
      cases h
  | succ n =>
      exact largeSchroeder_succ_eq_two_small n

theorem largeSchroeder_succ_from_small (n : Nat) :
    largeSchroederNumber (Nat.succ n) =
      2 * smallSchroederNumber (Nat.succ n) := by
  rfl

theorem largeSchroeder_succ_from_small_strong (n : Nat) :
    largeSchroederNumber (Nat.succ n) =
      2 * smallSchroederNumber (Nat.succ n) := by
  exact Nat.strongRecOn n
    (motive := fun k =>
      largeSchroederNumber (Nat.succ k) =
        2 * smallSchroederNumber (Nat.succ k))
    (fun k _ih => largeSchroeder_succ_from_small k)

theorem largeSchroeder_succ_succ_recursion_from_small (n : Nat) :
    largeSchroederNumber (Nat.succ (Nat.succ n)) =
      2 * (3 * smallSchroederNumber (Nat.succ n) +
        2 * smallSchroederInternalConvolution (Nat.succ n)) := by
  rw [largeSchroeder_succ_eq_two_small (Nat.succ n)]
  rw [smallSchroeder_succ_succ_recursion_strong n]

theorem largeSchroeder_convolution_small_values :
    largeSchroederConvolution 0 = 1 ∧ largeSchroederConvolution 1 = 4 ∧
      largeSchroederConvolution 2 = 16 ∧ largeSchroederConvolution 3 = 68 := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · rfl

theorem largeSchroeder_recurrence_small_values :
    largeSchroederNumber 1 =
        largeSchroederNumber 0 + largeSchroederConvolution 0 ∧
      largeSchroederNumber 2 =
        largeSchroederNumber 1 + largeSchroederConvolution 1 ∧
      largeSchroederNumber 3 =
        largeSchroederNumber 2 + largeSchroederConvolution 2 ∧
      largeSchroederNumber 4 =
        largeSchroederNumber 3 + largeSchroederConvolution 3 := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · rfl

theorem largeSchroederNumberFn_unary_result (n : BHist) :
    UnaryHistory (largeSchroederNumberFn n) := by
  unfold largeSchroederNumberFn
  exact natToUnary_unary _

theorem smallSchroederNumberFn_unary_result (n : BHist) :
    UnaryHistory (smallSchroederNumberFn n) := by
  unfold smallSchroederNumberFn
  exact natToUnary_unary _

theorem largeSchroederNumberFn_natToUnary (n : Nat) :
    largeSchroederNumberFn (natToUnary n) =
      natToUnary (largeSchroederNumber n) := by
  unfold largeSchroederNumberFn
  rw [natToUnary_length]

theorem smallSchroederNumberFn_natToUnary (n : Nat) :
    smallSchroederNumberFn (natToUnary n) =
      natToUnary (smallSchroederNumber n) := by
  unfold smallSchroederNumberFn
  rw [natToUnary_length]

theorem largeSchroeder_small_values :
    largeSchroederNumber 0 = 1 ∧ largeSchroederNumber 1 = 2 ∧
      largeSchroederNumber 2 = 6 ∧ largeSchroederNumber 3 = 22 ∧
        largeSchroederNumber 4 = 90 ∧ largeSchroederNumber 5 = 394 := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · rfl
        · constructor
          · rfl
          · rfl

theorem smallSchroeder_small_values :
    smallSchroederNumber 0 = 1 ∧ smallSchroederNumber 1 = 1 ∧
      smallSchroederNumber 2 = 3 ∧ smallSchroederNumber 3 = 11 ∧
        smallSchroederNumber 4 = 45 ∧ smallSchroederNumber 5 = 197 := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · rfl
        · constructor
          · rfl
          · rfl

theorem largeSchroeder_catalan_initial_contact :
    largeSchroederNumber 0 = catalanNumber 0 ∧
      largeSchroederNumber 1 = 2 * catalanNumber 1 := by
  constructor
  · rfl
  · rfl

theorem smallSchroeder_catalan_initial_contact :
    smallSchroederNumber 0 = catalanNumber 0 ∧
      smallSchroederNumber 1 = catalanNumber 1 := by
  constructor
  · rfl
  · rfl

theorem smallSchroeder_motzkin_initial_contact :
    smallSchroederNumber 0 = motzkinNumber 0 ∧
      smallSchroederNumber 1 = motzkinNumber 1 := by
  constructor
  · rfl
  · rfl

theorem empty_largeSchroederPath :
    LargeSchroederPath 0 [] := by
  exact SchroederWalk.nil

theorem diag_largeSchroederPath_one :
    LargeSchroederPath 1 [SchroederStep.diag] := by
  exact SchroederWalk.diag SchroederWalk.nil

theorem east_north_largeSchroederPath_one :
    LargeSchroederPath 1 [SchroederStep.east, SchroederStep.north] := by
  exact SchroederWalk.east (SchroederWalk.north SchroederWalk.nil)

theorem north_east_largeSchroederPath_one :
    LargeSchroederPath 1 [SchroederStep.north, SchroederStep.east] := by
  exact SchroederWalk.north (SchroederWalk.east SchroederWalk.nil)

theorem smallSchroederWalk_to_schroederWalk {started : Bool}
    {x y finishX finishY : Nat} {steps : List SchroederStep} :
    SmallSchroederWalk started x y steps finishX finishY ->
      SchroederWalk x y steps finishX finishY := by
  intro walk
  induction walk with
  | nil =>
      exact SchroederWalk.nil
  | east tailWalk ih =>
      exact SchroederWalk.east ih
  | north tailWalk ih =>
      exact SchroederWalk.north ih
  | diag tailWalk ih =>
      exact SchroederWalk.diag ih

theorem smallSchroederPath_to_largeSchroederPath {n : Nat}
    {steps : List SchroederStep} :
    SmallSchroederPath n steps -> LargeSchroederPath n steps := by
  intro path
  unfold SmallSchroederPath at path
  exact smallSchroederWalk_to_schroederWalk path

theorem empty_smallSchroederPath :
    SmallSchroederPath 0 [] := by
  unfold SmallSchroederPath
  exact SmallSchroederWalk.nil

theorem east_north_smallSchroederPath_one :
    SmallSchroederPath 1 [SchroederStep.east, SchroederStep.north] := by
  unfold SmallSchroederPath
  exact SmallSchroederWalk.east
    (SmallSchroederWalk.north SmallSchroederWalk.nil)

theorem diag_smallSchroederPath_one_refusal :
    ¬ SmallSchroederPath 1 [SchroederStep.diag] := by
  intro h
  unfold SmallSchroederPath at h
  cases h

theorem schroeder_path_surface_examples :
    LargeSchroederPath 0 [] ∧
      LargeSchroederPath 1 [SchroederStep.diag] ∧
        LargeSchroederPath 1 [SchroederStep.east, SchroederStep.north] ∧
          SmallSchroederPath 1 [SchroederStep.east, SchroederStep.north] ∧
            ¬ SmallSchroederPath 1 [SchroederStep.diag] := by
  constructor
  · exact empty_largeSchroederPath
  · constructor
    · exact diag_largeSchroederPath_one
    · constructor
      · exact east_north_largeSchroederPath_one
      · constructor
        · exact east_north_smallSchroederPath_one
        · exact diag_smallSchroederPath_one_refusal

theorem SchroederNumberUp_constructive_export :
    largeSchroederNumber 0 = 1 ∧
      (∀ n : Nat,
        largeSchroederNumber (Nat.succ n) =
          2 * smallSchroederNumber (Nat.succ n)) ∧
      smallSchroederNumber 0 = 1 ∧ smallSchroederNumber 1 = 1 ∧
      (∀ n : Nat,
        smallSchroederNumber (Nat.succ (Nat.succ n)) =
          3 * smallSchroederNumber (Nat.succ n) +
            2 * smallSchroederInternalConvolution (Nat.succ n)) ∧
      (∀ n : Nat,
        largeSchroederNumber (Nat.succ (Nat.succ n)) =
          2 * (3 * smallSchroederNumber (Nat.succ n) +
            2 * smallSchroederInternalConvolution (Nat.succ n))) ∧
      largeSchroederNumber 5 = 394 ∧ smallSchroederNumber 5 = 197 ∧
      largeSchroederNumber 0 = catalanNumber 0 ∧
      smallSchroederNumber 1 = motzkinNumber 1 ∧
      (∀ n : BHist, UnaryHistory (largeSchroederNumberFn n)) ∧
      (∀ n : BHist, UnaryHistory (smallSchroederNumberFn n)) ∧
      LargeSchroederPath 1 [SchroederStep.diag] ∧
      SmallSchroederPath 1 [SchroederStep.east, SchroederStep.north] := by
  constructor
  · exact largeSchroeder_zero
  · constructor
    · intro n
      exact largeSchroeder_succ_from_small_strong n
    · constructor
      · exact smallSchroeder_zero
      · constructor
        · exact smallSchroeder_one
        · constructor
          · intro n
            exact smallSchroeder_succ_succ_recursion_strong n
          · constructor
            · intro n
              exact largeSchroeder_succ_succ_recursion_from_small n
            · constructor
              · exact largeSchroeder_small_values.right.right.right.right.right
              · constructor
                · exact smallSchroeder_small_values.right.right.right.right.right
                · constructor
                  · exact largeSchroeder_catalan_initial_contact.left
                  · constructor
                    · exact smallSchroeder_motzkin_initial_contact.right
                    · constructor
                      · intro n
                        exact largeSchroederNumberFn_unary_result n
                      · constructor
                        · intro n
                          exact smallSchroederNumberFn_unary_result n
                        · constructor
                          · exact diag_largeSchroederPath_one
                          · exact east_north_smallSchroederPath_one

end BEDC.Derived.SchroederNumberUp
