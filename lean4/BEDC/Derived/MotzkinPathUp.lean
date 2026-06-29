import BEDC.Derived.CatalanUp
import BEDC.Derived.IntUp.Arithmetic

namespace BEDC.Derived.MotzkinPathUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.IntUp (natToUnary natToUnary_unary natToUnary_length)

inductive MotzkinStep : Type where
  | up : MotzkinStep
  | level : MotzkinStep
  | down : MotzkinStep

def stepLength : List MotzkinStep -> Nat
  | [] => 0
  | _ :: steps => Nat.succ (stepLength steps)

inductive MotzkinWalk : Nat -> List MotzkinStep -> Nat -> Prop where
  | nil {height : Nat} :
      MotzkinWalk height [] height
  | up {height finish : Nat} {tail : List MotzkinStep} :
      MotzkinWalk (Nat.succ height) tail finish ->
        MotzkinWalk height (MotzkinStep.up :: tail) finish
  | level {height finish : Nat} {tail : List MotzkinStep} :
      MotzkinWalk height tail finish ->
        MotzkinWalk height (MotzkinStep.level :: tail) finish
  | down {height finish : Nat} {tail : List MotzkinStep} :
      MotzkinWalk height tail finish ->
        MotzkinWalk (Nat.succ height) (MotzkinStep.down :: tail) finish

def MotzkinPath (steps : List MotzkinStep) : Prop :=
  MotzkinWalk 0 steps 0

def MotzkinPathOfLength (n : Nat) (steps : List MotzkinStep) : Prop :=
  MotzkinPath steps ∧ stepLength steps = n

inductive CatalanPath : List MotzkinStep -> Prop where
  | empty : CatalanPath []
  | wrap (middle tail : List MotzkinStep) :
      CatalanPath middle -> CatalanPath tail ->
        CatalanPath (MotzkinStep.up :: middle ++ MotzkinStep.down :: tail)

inductive LevelFree : List MotzkinStep -> Prop where
  | nil : LevelFree []
  | up {tail : List MotzkinStep} :
      LevelFree tail -> LevelFree (MotzkinStep.up :: tail)
  | down {tail : List MotzkinStep} :
      LevelFree tail -> LevelFree (MotzkinStep.down :: tail)

theorem motzkinWalk_lift {start finish : Nat} {steps : List MotzkinStep} :
    MotzkinWalk start steps finish ->
      MotzkinWalk (Nat.succ start) steps (Nat.succ finish) := by
  intro walk
  induction walk with
  | nil =>
      exact MotzkinWalk.nil
  | up tailWalk ih =>
      exact MotzkinWalk.up ih
  | level tailWalk ih =>
      exact MotzkinWalk.level ih
  | down tailWalk ih =>
      exact MotzkinWalk.down ih

theorem motzkinWalk_append {start middle finish : Nat}
    {left right : List MotzkinStep} :
    MotzkinWalk start left middle -> MotzkinWalk middle right finish ->
      MotzkinWalk start (left ++ right) finish := by
  intro leftWalk rightWalk
  induction leftWalk with
  | nil =>
      exact rightWalk
  | up tailWalk ih =>
      exact MotzkinWalk.up (ih rightWalk)
  | level tailWalk ih =>
      exact MotzkinWalk.level (ih rightWalk)
  | down tailWalk ih =>
      exact MotzkinWalk.down (ih rightWalk)

theorem empty_motzkinPath :
    MotzkinPath [] := by
  exact MotzkinWalk.nil

theorem level_motzkinPath :
    MotzkinPath [MotzkinStep.level] := by
  exact MotzkinWalk.level MotzkinWalk.nil

theorem up_down_motzkinPath :
    MotzkinPath [MotzkinStep.up, MotzkinStep.down] := by
  exact MotzkinWalk.up (MotzkinWalk.down MotzkinWalk.nil)

theorem catalanPath_to_motzkinPath {steps : List MotzkinStep} :
    CatalanPath steps -> MotzkinPath steps := by
  intro path
  induction path with
  | empty =>
      exact empty_motzkinPath
  | wrap middle tail middlePath tailPath middleWalk tailWalk =>
      have liftedMiddle : MotzkinWalk 1 middle 1 :=
        motzkinWalk_lift middleWalk
      have downTail : MotzkinWalk 1 (MotzkinStep.down :: tail) 0 :=
        MotzkinWalk.down tailWalk
      have joined : MotzkinWalk 1 (middle ++ MotzkinStep.down :: tail) 0 :=
        motzkinWalk_append liftedMiddle downTail
      exact MotzkinWalk.up joined

private theorem levelFree_append_down :
    ∀ middle tail : List MotzkinStep,
      LevelFree middle -> LevelFree tail ->
        LevelFree (middle ++ MotzkinStep.down :: tail)
  | [], _tail, _middleFree, tailFree =>
      LevelFree.down tailFree
  | MotzkinStep.up :: rest, tail, middleFree, tailFree =>
      have restFree : LevelFree rest := by
        cases middleFree with
        | up restFree =>
            exact restFree
      LevelFree.up (levelFree_append_down rest tail restFree tailFree)
  | MotzkinStep.level :: _rest, _tail, middleFree, _tailFree =>
      by cases middleFree
  | MotzkinStep.down :: rest, tail, middleFree, tailFree =>
      have restFree : LevelFree rest := by
        cases middleFree with
        | down restFree =>
            exact restFree
      LevelFree.down (levelFree_append_down rest tail restFree tailFree)

theorem catalanPath_levelFree {steps : List MotzkinStep} :
    CatalanPath steps -> LevelFree steps := by
  intro path
  induction path with
  | empty =>
      exact LevelFree.nil
  | wrap middle tail middlePath tailPath middleFree tailFree =>
      exact LevelFree.up (levelFree_append_down middle tail middleFree tailFree)

def listLen {A : Type} : List A -> Nat
  | [] => 0
  | _ :: tail => Nat.succ (listLen tail)

def listNthNat : List Nat -> Nat -> Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: tail, Nat.succ n => listNthNat tail n

def listNatSum : List Nat -> Nat
  | [] => 0
  | x :: tail => x + listNatSum tail

def natRangeFuel : Nat -> Nat -> List Nat
  | 0, _start => []
  | Nat.succ fuel, start => start :: natRangeFuel fuel (Nat.succ start)

def motzkinConvolutionFromPrefix
    (pref : List Nat) : Nat -> Nat -> Nat -> Nat
  | 0, _index, _top => 0
  | Nat.succ fuel, index, top =>
      listNthNat pref index * listNthNat pref (top - index) +
        motzkinConvolutionFromPrefix pref fuel (Nat.succ index) top

def motzkinPrefixConvolution (pref : List Nat) : Nat -> Nat
  | 0 => 0
  | Nat.succ top => motzkinConvolutionFromPrefix pref (Nat.succ top) 0 top

def motzkinPrefix : Nat -> List Nat
  | 0 => [1]
  | Nat.succ n =>
      let pref := motzkinPrefix n
      pref ++ [listNthNat pref n + motzkinPrefixConvolution pref n]

def motzkinNumber (n : Nat) : Nat :=
  listNthNat (motzkinPrefix n) n

def motzkinRecurrenceConvolutionFrom : Nat -> Nat -> Nat -> Nat
  | 0, _index, _top => 0
  | Nat.succ fuel, index, top =>
      motzkinNumber index * motzkinNumber (top - index) +
        motzkinRecurrenceConvolutionFrom fuel (Nat.succ index) top

def motzkinRecurrenceConvolution : Nat -> Nat
  | 0 => 0
  | Nat.succ top => motzkinRecurrenceConvolutionFrom (Nat.succ top) 0 top

def motzkinNumberFn (n : BHist) : BHist :=
  natToUnary (motzkinNumber (bwordLength n))

theorem listLen_append_singleton {A : Type} (xs : List A) (x : A) :
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

theorem motzkinPrefix_listLen (n : Nat) :
    listLen (motzkinPrefix n) = Nat.succ n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      exact Eq.trans
        (listLen_append_singleton (motzkinPrefix n)
          (listNthNat (motzkinPrefix n) n +
            motzkinPrefixConvolution (motzkinPrefix n) n))
        (congrArg Nat.succ ih)

theorem listNthNat_append_at_succ_of_listLen (xs : List Nat) (x n : Nat)
    (h : listLen xs = Nat.succ n) :
    listNthNat (xs ++ [x]) (Nat.succ n) = x := by
  exact Eq.ndrec (motive := fun k => listNthNat (xs ++ [x]) k = x)
    (listNthNat_append_at_listLen xs x) h

theorem motzkin_zero :
    motzkinNumber 0 = 1 := by
  rfl

theorem motzkin_succ_prefix_recursion (n : Nat) :
    motzkinNumber (Nat.succ n) =
      motzkinNumber n + motzkinPrefixConvolution (motzkinPrefix n) n := by
  exact listNthNat_append_at_succ_of_listLen
    (motzkinPrefix n)
    (listNthNat (motzkinPrefix n) n +
      motzkinPrefixConvolution (motzkinPrefix n) n)
    n
    (motzkinPrefix_listLen n)

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

theorem motzkinPrefix_nth_stable_add (i extra : Nat) :
    listNthNat (motzkinPrefix (i + extra)) i = motzkinNumber i := by
  induction extra with
  | zero =>
      rw [Nat.add_zero]
      rfl
  | succ extra ih =>
      rw [Nat.add_succ]
      change
        listNthNat
            (motzkinPrefix (i + extra) ++
              [listNthNat (motzkinPrefix (i + extra)) (i + extra) +
                motzkinPrefixConvolution (motzkinPrefix (i + extra)) (i + extra)])
            i =
          motzkinNumber i
      rw [listNthNat_append_left_of_lt_listLen
        (motzkinPrefix (i + extra))
        [listNthNat (motzkinPrefix (i + extra)) (i + extra) +
          motzkinPrefixConvolution (motzkinPrefix (i + extra)) (i + extra)]
        i]
      · exact ih
      · rw [motzkinPrefix_listLen]
        exact lt_succ_add_right i extra

private theorem le_to_add_tail {i n : Nat} :
    i <= n -> ∃ extra : Nat, n = i + extra := by
  intro h
  obtain ⟨extra, hEq⟩ := Nat.le.dest h
  exact ⟨extra, hEq.symm⟩

theorem motzkinPrefix_nth_stable_of_le {i n : Nat} (h : i <= n) :
    listNthNat (motzkinPrefix n) i = motzkinNumber i := by
  obtain ⟨extra, hEq⟩ := le_to_add_tail h
  rw [hEq]
  exact motzkinPrefix_nth_stable_add i extra

private theorem motzkinConvolutionFromPrefix_eq_numberFrom :
    ∀ fuel index top bound : Nat,
      top <= bound ->
      index + fuel = Nat.succ top ->
        motzkinConvolutionFromPrefix (motzkinPrefix bound) fuel index top =
          motzkinRecurrenceConvolutionFrom fuel index top
  | 0, _index, _top, _bound, _topLeBound, _sumBound => by
      rfl
  | Nat.succ fuel, index, top, bound, topLeBound, sumBound => by
      change
        listNthNat (motzkinPrefix bound) index *
            listNthNat (motzkinPrefix bound) (top - index) +
            motzkinConvolutionFromPrefix (motzkinPrefix bound) fuel
              (Nat.succ index) top =
          motzkinNumber index * motzkinNumber (top - index) +
            motzkinRecurrenceConvolutionFrom fuel (Nat.succ index) top
      have sumEq : index + fuel = top := by
        have shifted : Nat.succ (index + fuel) = Nat.succ top := by
          rw [Nat.add_succ] at sumBound
          exact sumBound
        exact Nat.succ.inj shifted
      have indexLe : index <= top := by
        have raw : index <= index + fuel := nat_le_add_right_self index fuel
        rw [sumEq] at raw
        exact raw
      have indexLeBound : index <= bound :=
        Nat.le_trans indexLe topLeBound
      have tailLe : top - index <= top :=
        Nat.sub_le top index
      have tailLeBound : top - index <= bound :=
        Nat.le_trans tailLe topLeBound
      rw [motzkinPrefix_nth_stable_of_le indexLeBound]
      rw [motzkinPrefix_nth_stable_of_le tailLeBound]
      have nextBound : Nat.succ index + fuel = Nat.succ top := by
        rw [Nat.succ_add]
        rw [sumEq]
      rw [motzkinConvolutionFromPrefix_eq_numberFrom fuel
        (Nat.succ index) top bound topLeBound nextBound]

theorem motzkinConvolution_eq_recurrence (n : Nat) :
    motzkinPrefixConvolution (motzkinPrefix n) n =
      motzkinRecurrenceConvolution n := by
  cases n with
  | zero =>
      rfl
  | succ top =>
      exact motzkinConvolutionFromPrefix_eq_numberFrom
        (Nat.succ top) 0 top (Nat.succ top) (Nat.le_succ top)
        (Nat.zero_add (Nat.succ top))

theorem motzkin_succ_recursion (n : Nat) :
    motzkinNumber (Nat.succ n) =
      motzkinNumber n + motzkinRecurrenceConvolution n := by
  rw [motzkin_succ_prefix_recursion n]
  rw [motzkinConvolution_eq_recurrence n]

theorem motzkin_succ_recursion_strong (n : Nat) :
    motzkinNumber (Nat.succ n) =
      motzkinNumber n + motzkinRecurrenceConvolution n := by
  exact Nat.strongRecOn n
    (motive := fun k =>
      motzkinNumber (Nat.succ k) =
        motzkinNumber k + motzkinRecurrenceConvolution k)
    (fun k _ih => motzkin_succ_recursion k)

theorem motzkinNumberFn_unary_result (n : BHist) :
    UnaryHistory (motzkinNumberFn n) := by
  unfold motzkinNumberFn
  exact natToUnary_unary _

theorem motzkinNumberFn_natToUnary (n : Nat) :
    motzkinNumberFn (natToUnary n) = natToUnary (motzkinNumber n) := by
  unfold motzkinNumberFn
  rw [natToUnary_length]

theorem motzkin_small_values :
    motzkinNumber 0 = 1 ∧ motzkinNumber 1 = 1 ∧
      motzkinNumber 2 = 2 ∧ motzkinNumber 3 = 4 ∧
        motzkinNumber 4 = 9 ∧ motzkinNumber 5 = 21 ∧
          motzkinNumber 6 = 51 := by
  constructor
  · rfl
  · constructor
    · decide
    · constructor
      · decide
      · constructor
        · decide
        · constructor
          · decide
          · constructor
            · decide
            · decide

theorem motzkin_path_small_witnesses :
    MotzkinPath [] ∧ MotzkinPath [MotzkinStep.level] ∧
      MotzkinPath [MotzkinStep.up, MotzkinStep.down] := by
  constructor
  · exact empty_motzkinPath
  · constructor
    · exact level_motzkinPath
    · exact up_down_motzkinPath

theorem catalan_initial_bridge :
    BEDC.Derived.CatalanUp.Catalan BHist.Empty
        BEDC.Derived.CatalanUp.NatOne ∧
      CatalanPath [] ∧ MotzkinPath [] := by
  constructor
  · exact BEDC.Derived.CatalanUp.catalan_zero
  · constructor
    · exact CatalanPath.empty
    · exact empty_motzkinPath

theorem MotzkinPathUp_constructive_export :
    motzkinNumber 0 = 1 ∧
      (∀ n : Nat,
        motzkinNumber (Nat.succ n) =
          motzkinNumber n + motzkinRecurrenceConvolution n) ∧
      (∀ steps : List MotzkinStep, CatalanPath steps -> MotzkinPath steps) ∧
      (∀ steps : List MotzkinStep, CatalanPath steps -> LevelFree steps) ∧
      motzkinNumber 0 = 1 ∧ motzkinNumber 1 = 1 ∧
        motzkinNumber 2 = 2 ∧ motzkinNumber 3 = 4 ∧
          motzkinNumber 4 = 9 ∧ motzkinNumber 5 = 21 ∧
            motzkinNumber 6 = 51 ∧
            (∀ n : BHist, UnaryHistory (motzkinNumberFn n)) ∧
            (BEDC.Derived.CatalanUp.Catalan BHist.Empty
                BEDC.Derived.CatalanUp.NatOne ∧
              CatalanPath [] ∧ MotzkinPath []) := by
  constructor
  · exact motzkin_zero
  · constructor
    · intro n
      exact motzkin_succ_recursion_strong n
    · constructor
      · intro steps path
        exact catalanPath_to_motzkinPath path
      · constructor
        · intro steps path
          exact catalanPath_levelFree path
        · constructor
          · exact motzkin_small_values.left
          · constructor
            · exact motzkin_small_values.right.left
            · constructor
              · exact motzkin_small_values.right.right.left
              · constructor
                · exact motzkin_small_values.right.right.right.left
                · constructor
                  · exact motzkin_small_values.right.right.right.right.left
                  · constructor
                    · exact motzkin_small_values.right.right.right.right.right.left
                    · constructor
                      · exact motzkin_small_values.right.right.right.right.right.right
                      · constructor
                        · intro n
                          exact motzkinNumberFn_unary_result n
                        · exact catalan_initial_bridge

end BEDC.Derived.MotzkinPathUp
