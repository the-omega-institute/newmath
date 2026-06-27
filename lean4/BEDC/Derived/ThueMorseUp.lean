import BEDC.Algebra.FiniteFold
import BEDC.Derived.NatUp

namespace BEDC.Derived.ThueMorseUp

inductive Bit where
  | zero : Bit
  | one : Bit

namespace Bit

def flip : Bit -> Bit
  | zero => one
  | one => zero

def eqBool : Bit -> Bit -> Bool
  | zero, zero => true
  | zero, one => false
  | one, zero => false
  | one, one => true

theorem flip_flip (b : Bit) : flip (flip b) = b := by
  cases b
  · rfl
  · rfl

end Bit

abbrev BWord := List Bit

def natParity : Nat -> Bit
  | 0 => Bit.zero
  | Nat.succ n => Bit.flip (natParity n)

def bitToNat : Bit -> Nat
  | Bit.zero => 0
  | Bit.one => 1

def evalWord : BWord -> Nat
  | [] => 0
  | Bit.zero :: rest => 2 * evalWord rest
  | Bit.one :: rest => 2 * evalWord rest + 1

def popcount : BWord -> Nat
  | [] => 0
  | Bit.zero :: rest => popcount rest
  | Bit.one :: rest => Nat.succ (popcount rest)

def thueMorse : BWord -> Bit
  | [] => Bit.zero
  | Bit.zero :: rest => thueMorse rest
  | Bit.one :: rest => Bit.flip (thueMorse rest)

def doubleWord (w : BWord) : BWord :=
  Bit.zero :: w

def doubleAddOneWord (w : BWord) : BWord :=
  Bit.one :: w

def incrementWord : BWord -> BWord
  | [] => [Bit.one]
  | Bit.zero :: rest => Bit.one :: rest
  | Bit.one :: rest => Bit.zero :: incrementWord rest

def natWord : Nat -> BWord
  | 0 => []
  | Nat.succ n => incrementWord (natWord n)

def modTwo : Nat -> Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => modTwo n

def popcountParity (w : BWord) : Nat :=
  modTwo (popcount w)

def natPopcount (n : Nat) : Nat :=
  popcount (natWord n)

def thueMorseNat (n : Nat) : Bit :=
  thueMorse (natWord n)

theorem natParity_succ (n : Nat) :
    natParity (Nat.succ n) = Bit.flip (natParity n) := by
  rfl

theorem bitToNat_flip_add_self (b : Bit) :
    bitToNat (Bit.flip b) + bitToNat b = 1 := by
  cases b
  · rfl
  · rfl

theorem bitToNat_natParity_eq_modTwo :
    ∀ n : Nat, bitToNat (natParity n) = modTwo n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      change bitToNat (Bit.flip (Bit.flip (natParity n))) = modTwo n
      rw [Bit.flip_flip]
      exact bitToNat_natParity_eq_modTwo n

theorem thueMorse_eq_popcount_parity (w : BWord) :
    thueMorse w = natParity (popcount w) := by
  induction w with
  | nil =>
      rfl
  | cons b rest ih =>
      cases b with
      | zero =>
          exact ih
      | one =>
          change Bit.flip (thueMorse rest) = Bit.flip (natParity (popcount rest))
          exact congrArg Bit.flip ih

theorem thueMorse_value_eq_popcount_modTwo (w : BWord) :
    bitToNat (thueMorse w) = popcountParity w := by
  rw [thueMorse_eq_popcount_parity]
  exact bitToNat_natParity_eq_modTwo (popcount w)

theorem evalWord_doubleWord (w : BWord) :
    evalWord (doubleWord w) = 2 * evalWord w := by
  rfl

theorem evalWord_doubleAddOneWord (w : BWord) :
    evalWord (doubleAddOneWord w) = 2 * evalWord w + 1 := by
  rfl

theorem evalWord_incrementWord (w : BWord) :
    evalWord (incrementWord w) = Nat.succ (evalWord w) := by
  induction w with
  | nil =>
      rfl
  | cons b rest ih =>
      cases b with
      | zero =>
          rfl
      | one =>
          change 2 * evalWord (incrementWord rest) = Nat.succ (2 * evalWord rest + 1)
          rw [ih]
          rw [Nat.mul_succ]

theorem evalWord_natWord :
    ∀ n : Nat, evalWord (natWord n) = n
  | 0 =>
      rfl
  | Nat.succ n => by
      change evalWord (incrementWord (natWord n)) = Nat.succ n
      rw [evalWord_incrementWord]
      exact congrArg Nat.succ (evalWord_natWord n)

theorem popcount_doubleWord (w : BWord) :
    popcount (doubleWord w) = popcount w := by
  rfl

theorem popcount_doubleAddOneWord (w : BWord) :
    popcount (doubleAddOneWord w) = Nat.succ (popcount w) := by
  rfl

theorem thueMorse_even_double (w : BWord) :
    thueMorse (doubleWord w) = thueMorse w := by
  rfl

theorem thueMorse_odd_double_flip (w : BWord) :
    thueMorse (doubleAddOneWord w) = Bit.flip (thueMorse w) := by
  rfl

theorem thueMorse_odd_double_value_complement (w : BWord) :
    bitToNat (thueMorse (doubleAddOneWord w)) +
        bitToNat (thueMorse w) = 1 := by
  exact bitToNat_flip_add_self (thueMorse w)

theorem thueMorseNat_eq_natPopcount_parity (n : Nat) :
    thueMorseNat n = natParity (natPopcount n) := by
  exact thueMorse_eq_popcount_parity (natWord n)

theorem thueMorseNat_value_eq_natPopcount_modTwo (n : Nat) :
    bitToNat (thueMorseNat n) = modTwo (natPopcount n) := by
  exact thueMorse_value_eq_popcount_modTwo (natWord n)

def IsCubeFactor (word : BWord) : Prop :=
  exists pre : BWord, exists block : BWord, exists post : BWord,
    (block = [] -> False) /\ word = pre ++ block ++ block ++ block ++ post

def CubeFree (word : BWord) : Prop :=
  IsCubeFactor word -> False

def IsOverlapFactor (word : BWord) : Prop :=
  exists pre : BWord, exists a : Bit, exists middle : BWord, exists post : BWord,
    word = pre ++ [a] ++ middle ++ [a] ++ middle ++ [a] ++ post

def OverlapFree (word : BWord) : Prop :=
  IsOverlapFactor word -> False

def morphBit : Bit -> BWord
  | Bit.zero => [Bit.zero, Bit.one]
  | Bit.one => [Bit.one, Bit.zero]

def morphWord : BWord -> BWord
  | [] => []
  | b :: rest => morphBit b ++ morphWord rest

def thueMorsePrefix : Nat -> BWord
  | 0 => [Bit.zero]
  | Nat.succ n => morphWord (thueMorsePrefix n)

def indicesOfSymbolFrom : Nat -> Bit -> BWord -> List Nat
  | _idx, _target, [] => []
  | idx, target, b :: rest =>
      if Bit.eqBool target b then
        idx :: indicesOfSymbolFrom (Nat.succ idx) target rest
      else
        indicesOfSymbolFrom (Nat.succ idx) target rest

def indicesOfSymbol (target : Bit) (word : BWord) : List Nat :=
  indicesOfSymbolFrom 0 target word

def natPow : Nat -> Nat -> Nat
  | _base, 0 => 1
  | base, Nat.succ exponent => base * natPow base exponent

def natListPowerSum (exponent : Nat) : List Nat -> Nat
  | [] => 0
  | n :: rest => natPow n exponent + natListPowerSum exponent rest

theorem thueMorsePrefix_two_shape :
    thueMorsePrefix 2 = [Bit.zero, Bit.one, Bit.one, Bit.zero] := by
  rfl

theorem thueMorsePrefix_two_zero_indices :
    indicesOfSymbol Bit.zero (thueMorsePrefix 2) = [0, 3] := by
  rfl

theorem thueMorsePrefix_two_one_indices :
    indicesOfSymbol Bit.one (thueMorsePrefix 2) = [1, 2] := by
  rfl

theorem thueMorsePrefix_two_index_lists_finite :
    List.Nodup (indicesOfSymbol Bit.zero (thueMorsePrefix 2)) /\
      List.Nodup (indicesOfSymbol Bit.one (thueMorsePrefix 2)) /\
      List.count 0 (indicesOfSymbol Bit.zero (thueMorsePrefix 2)) = 1 /\
      List.count 3 (indicesOfSymbol Bit.zero (thueMorsePrefix 2)) = 1 /\
      List.count 1 (indicesOfSymbol Bit.one (thueMorsePrefix 2)) = 1 /\
      List.count 2 (indicesOfSymbol Bit.one (thueMorsePrefix 2)) = 1 := by
  constructor
  · decide
  · constructor
    · decide
    · constructor
      · rfl
      · constructor
        · rfl
        · constructor
          · rfl
          · rfl

theorem thueMorse_pte_level_two_order_one :
    natListPowerSum 0 (indicesOfSymbol Bit.zero (thueMorsePrefix 2)) =
        natListPowerSum 0 (indicesOfSymbol Bit.one (thueMorsePrefix 2)) /\
      natListPowerSum 1 (indicesOfSymbol Bit.zero (thueMorsePrefix 2)) =
        natListPowerSum 1 (indicesOfSymbol Bit.one (thueMorsePrefix 2)) := by
  constructor
  · rfl
  · rfl

end BEDC.Derived.ThueMorseUp
