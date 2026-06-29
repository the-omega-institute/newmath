import BEDC.Derived.FibonacciUp

namespace BEDC.Derived.FibonacciWordUp

abbrev FibonacciNat : Nat -> Nat :=
  BEDC.Derived.FibonacciUp.fib

def fibonacciWord : Nat -> List Bool
  | 0 => []
  | 1 => [false]
  | 2 => [true]
  | n + 3 => fibonacciWord (n + 2) ++ fibonacciWord (n + 1)

def firstBit : List Bool -> Option Bool
  | [] => none
  | bit :: _ => some bit

def countTrue : List Bool -> Nat
  | [] => 0
  | true :: tail => countTrue tail + 1
  | false :: tail => countTrue tail

def boolEq (left right : Bool) : Bool :=
  match left with
  | false =>
      match right with
      | false => true
      | true => false
  | true =>
      match right with
      | false => false
      | true => true

def listBoolEq (left right : List Bool) : Bool :=
  match left with
  | [] =>
      match right with
      | [] => true
      | _ :: _ => false
  | x :: xs =>
      match right with
      | [] => false
      | y :: ys => boolEq x y && listBoolEq xs ys

def listBoolPrefixEq (prefixBits word : List Bool) : Bool :=
  match prefixBits with
  | [] => true
  | x :: xs =>
      match word with
      | [] => false
      | y :: ys => boolEq x y && listBoolPrefixEq xs ys

def natEqFuel (left right : Nat) : Bool :=
  match left with
  | 0 =>
      match right with
      | 0 => true
      | _ + 1 => false
  | a + 1 =>
      match right with
      | 0 => false
      | b + 1 => natEqFuel a b

def natWithinOneBool (left right : Nat) : Bool :=
  natEqFuel left right || natEqFuel (left + 1) right || natEqFuel (right + 1) left

inductive FactorIn (factor word : List Bool) : Prop where
  | here (pref suff : List Bool) :
      word = pref ++ factor ++ suff -> FactorIn factor word

def cubeBlock (block : List Bool) : List Bool :=
  block ++ block ++ block

def hasFactorFuel (fuel : Nat) (factor word : List Bool) : Bool :=
  match fuel with
  | 0 => false
  | next + 1 =>
      match word with
      | [] => listBoolPrefixEq factor []
      | x :: tail => listBoolPrefixEq factor (x :: tail) || hasFactorFuel next factor tail

def anyCubeFromBlocksFuel (factorFuel : Nat) :
    List (List Bool) -> List Bool -> Bool
  | [], _ => false
  | block :: blocks, word =>
      match word with
      | [] => false
      | _ :: _ =>
          match listBoolEq block [] with
          | true => anyCubeFromBlocksFuel factorFuel blocks word
          | false =>
              hasFactorFuel factorFuel (cubeBlock block) word ||
                anyCubeFromBlocksFuel factorFuel blocks word

def boundedCubeFreeByFuel
    (factorFuel : Nat) (candidateBlocks : List (List Bool)) (word : List Bool) : Prop :=
  anyCubeFromBlocksFuel factorFuel candidateBlocks word = false

def balancedPairBool (left right : List Bool) : Bool :=
  match natEqFuel left.length right.length with
  | true => natWithinOneBool (countTrue left) (countTrue right)
  | false => true

def allBalancedAgainst (left : List Bool) : List (List Bool) -> Bool
  | [] => true
  | right :: rest => balancedPairBool left right && allBalancedAgainst left rest

def allBalancedPairs : List (List Bool) -> Bool
  | [] => true
  | left :: rest => allBalancedAgainst left (left :: rest) && allBalancedPairs rest

def sturmianBalancedByFactorList (factors : List (List Bool)) : Prop :=
  allBalancedPairs factors = true

def CubeFree (word : List Bool) : Prop :=
  forall block : List Bool, block ≠ [] -> FactorIn (cubeBlock block) word -> False

def NatWithinOne (left right : Nat) : Prop :=
  left = right ∨ left + 1 = right ∨ right + 1 = left

def SturmianBalanced (word : List Bool) : Prop :=
  forall left right : List Bool,
    FactorIn left word ->
      FactorIn right word ->
        left.length = right.length -> NatWithinOne (countTrue left) (countTrue right)

private theorem list_length_append {A : Type} :
    forall xs ys : List A, (xs ++ ys).length = xs.length + ys.length
  | [], ys => (Nat.zero_add ys.length).symm
  | _ :: xs, ys =>
      (congrArg Nat.succ (list_length_append xs ys)).trans
        (Nat.succ_add xs.length ys.length).symm

theorem fibonacciWord_recurrence_from_one (n : Nat) :
    fibonacciWord (n + 3) = fibonacciWord (n + 2) ++ fibonacciWord (n + 1) := by
  rfl

theorem fibonacciWord_length_eq_fibonacci :
    forall n : Nat, (fibonacciWord n).length = FibonacciNat n
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | n + 3 => by
      change (fibonacciWord (n + 2) ++ fibonacciWord (n + 1)).length =
        FibonacciNat (n + 3)
      rw [list_length_append]
      rw [fibonacciWord_length_eq_fibonacci (n + 2)]
      rw [fibonacciWord_length_eq_fibonacci (n + 1)]
      unfold FibonacciNat
      exact (BEDC.Derived.FibonacciUp.fib_recurrence (n + 1)).symm

theorem firstBit_append_of_some {xs ys : List Bool} {bit : Bool} :
    firstBit xs = some bit -> firstBit (xs ++ ys) = some bit := by
  intro first
  cases xs with
  | nil =>
      cases first
  | cons _ _ =>
      exact first

theorem fibonacciWord_first_from_two :
    forall n : Nat, firstBit (fibonacciWord (n + 2)) = some true
  | 0 => rfl
  | n + 1 => by
      change firstBit (fibonacciWord (n + 3)) = some true
      rw [fibonacciWord_recurrence_from_one n]
      exact firstBit_append_of_some (fibonacciWord_first_from_two n)

theorem factorIn_empty_eq_nil {factor : List Bool} :
    FactorIn factor [] -> factor = [] := by
  intro occurrence
  cases occurrence with
  | here pref suff eq =>
      cases pref with
      | nil =>
          cases factor with
          | nil =>
              rfl
          | cons _ _ =>
              cases eq
      | cons _ _ =>
          cases eq

theorem empty_cubeFree : CubeFree [] := by
  intro block blockNonempty occurrence
  have cubeNil : cubeBlock block = [] := factorIn_empty_eq_nil occurrence
  cases block with
  | nil =>
      exact blockNonempty rfl
  | cons _ _ =>
      cases cubeNil

theorem fibonacciWord_zero_cubeFree : CubeFree (fibonacciWord 0) :=
  empty_cubeFree

theorem anyCubeFromBlocksFuel_empty_word (factorFuel : Nat)
    (candidateBlocks : List (List Bool)) :
    anyCubeFromBlocksFuel factorFuel candidateBlocks [] = false := by
  cases candidateBlocks with
  | nil =>
      rfl
  | cons _ _ =>
      rfl

theorem fibonacciWord_zero_boundedCubeFreeByFuel
    (factorFuel : Nat) (candidateBlocks : List (List Bool)) :
    boundedCubeFreeByFuel factorFuel candidateBlocks (fibonacciWord 0) := by
  exact anyCubeFromBlocksFuel_empty_word factorFuel candidateBlocks

theorem fibonacciWord_two_boundedCubeFree_singletons :
    boundedCubeFreeByFuel 2 [[false], [true]] (fibonacciWord 2) := by
  rfl

theorem empty_sturmianBalanced : SturmianBalanced [] := by
  intro left right leftIn rightIn _sameLength
  have leftNil : left = [] := factorIn_empty_eq_nil leftIn
  have rightNil : right = [] := factorIn_empty_eq_nil rightIn
  rw [leftNil, rightNil]
  exact Or.inl rfl

theorem fibonacciWord_zero_sturmianBalanced : SturmianBalanced (fibonacciWord 0) :=
  empty_sturmianBalanced

theorem empty_sturmianBalancedByFactorList :
    sturmianBalancedByFactorList [] := by
  rfl

theorem fibonacciWord_two_factorList_balanced :
    sturmianBalancedByFactorList [[], [true]] := by
  rfl

end BEDC.Derived.FibonacciWordUp
