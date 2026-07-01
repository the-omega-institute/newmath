namespace BEDC.Derived.Window6SignedInvolutionFixedPoint

/-!
This file packages a guarded Window6 sign-reversing involution with its
fixed-point certificate.  The proof object is the involution itself, not a
count-flatten, gluing, inequality, automaton-congruence, or recurrence anchor.
-/

structure Block6 where
  b0 : Bool
  b1 : Bool
  b2 : Bool
  b3 : Bool
  b4 : Bool
  b5 : Bool

def block6 (b0 b1 b2 b3 b4 b5 : Bool) : Block6 :=
  ⟨b0, b1, b2, b3, b4, b5⟩

def bxor (a b : Bool) : Bool :=
  if a then !b else b

def boolNat : Bool → Nat
  | false => 0
  | true => 1

def noAdj6 (b0 b1 b2 b3 b4 b5 : Bool) : Bool :=
  !(b0 && b1) && !(b1 && b2) && !(b2 && b3) && !(b3 && b4) && !(b4 && b5)

def noAdjBlock (b : Block6) : Bool :=
  noAdj6 b.b0 b.b1 b.b2 b.b3 b.b4 b.b5

def flip6 (b0 b1 b2 b3 b4 b5 : Bool) : Block6 :=
  if b1 then
    if b3 then
      block6 b0 b1 b2 false b4 b5
    else if b4 then
      block6 b0 b1 b2 b3 b4 b5
    else
      block6 b0 b1 b2 true b4 b5
  else
    block6 (!b0) b1 b2 b3 b4 b5

def flip6Block (b : Block6) : Block6 :=
  flip6 b.b0 b.b1 b.b2 b.b3 b.b4 b.b5

def ones6 (b0 b1 b2 b3 b4 b5 : Bool) : Nat :=
  boolNat b0 + boolNat b1 + boolNat b2 + boolNat b3 + boolNat b4 + boolNat b5

def parity6 (b0 b1 b2 b3 b4 b5 : Bool) : Bool :=
  bxor b0 (bxor b1 (bxor b2 (bxor b3 (bxor b4 b5))))

def parityBlock (b : Block6) : Bool :=
  parity6 b.b0 b.b1 b.b2 b.b3 b.b4 b.b5

theorem flip6_involutive
    (b0 b1 b2 b3 b4 b5 : Bool)
    (h : noAdj6 b0 b1 b2 b3 b4 b5 = true) :
    flip6Block (flip6 b0 b1 b2 b3 b4 b5) = block6 b0 b1 b2 b3 b4 b5 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;>
    unfold noAdj6 at h <;>
    unfold flip6Block flip6 block6 <;>
    cases h <;>
    rfl

theorem flip6_parity_flip
    (b0 b1 b2 b3 b4 b5 : Bool)
    (h : noAdj6 b0 b1 b2 b3 b4 b5 = true)
    (hne : block6 b0 b1 b2 b3 b4 b5 ≠ block6 false true false false true false) :
    parityBlock (flip6 b0 b1 b2 b3 b4 b5) ≠ parity6 b0 b1 b2 b3 b4 b5 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;>
    unfold noAdj6 at h <;>
    unfold block6 at hne <;>
    unfold parityBlock parity6 bxor flip6 block6 <;>
    cases h <;>
    intro hp <;>
    cases hp <;>
    apply hne <;>
    rfl

theorem flip6_fixed_010010 :
    flip6 false true false false true false = block6 false true false false true false := by
  rfl

theorem flip6_fixed_unique
    (b0 b1 b2 b3 b4 b5 : Bool)
    (h : noAdj6 b0 b1 b2 b3 b4 b5 = true)
    (hfix : flip6 b0 b1 b2 b3 b4 b5 = block6 b0 b1 b2 b3 b4 b5) :
    block6 b0 b1 b2 b3 b4 b5 = block6 false true false false true false := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;>
    unfold noAdj6 at h <;>
    unfold flip6 block6 at hfix <;>
    unfold block6 <;>
    cases h <;>
    cases hfix <;>
    rfl

theorem flip6_preserves_fib
    (b0 b1 b2 b3 b4 b5 : Bool)
    (h : noAdj6 b0 b1 b2 b3 b4 b5 = true) :
    noAdjBlock (flip6 b0 b1 b2 b3 b4 b5) = true := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;>
    unfold noAdj6 at h <;>
    unfold noAdjBlock flip6 block6 noAdj6 <;>
    cases h <;>
    rfl

def prependAll (b : Bool) : List (List Bool) → List (List Bool)
  | [] => []
  | w :: ws => (b :: w) :: prependAll b ws

def allWords : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => prependAll false (allWords n) ++ prependAll true (allWords n)

def bitAt : List Bool → Nat → Bool
  | [], _ => false
  | b :: _, 0 => b
  | _ :: bs, n + 1 => bitAt bs n

def hasNoAdj : List Bool → Bool
  | [] => true
  | [_] => true
  | a :: b :: bs => !(a && b) && hasNoAdj (b :: bs)

def natRangeFrom (start : Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => start :: natRangeFrom (start + 1) n

def natRange (n : Nat) : List Nat :=
  natRangeFrom 0 n

def startPositions (m : Nat) : List Nat :=
  natRange (m - 5)

def leftGuard (w : List Bool) : Nat → Bool
  | 0 => true
  | i + 1 => !bitAt w i

def rightGuard (w : List Bool) (i : Nat) : Bool :=
  !bitAt w (i + 6)

def guardedMark (w : List Bool) (i : Nat) : Bool :=
  hasNoAdj w && leftGuard w i && rightGuard w i

def parityAt (w : List Bool) (i : Nat) : Bool :=
  parity6
    (bitAt w i)
    (bitAt w (i + 1))
    (bitAt w (i + 2))
    (bitAt w (i + 3))
    (bitAt w (i + 4))
    (bitAt w (i + 5))

def fixedBlockAt (w : List Bool) (i : Nat) : Bool :=
  !(bitAt w i) &&
    bitAt w (i + 1) &&
    !(bitAt w (i + 2)) &&
    !(bitAt w (i + 3)) &&
    bitAt w (i + 4) &&
    !(bitAt w (i + 5))

def countNatList (p : Nat → Bool) : List Nat → Nat
  | [] => 0
  | i :: is => (if p i then 1 else 0) + countNatList p is

def countWordStarts (p : List Bool → Nat → Bool) (starts : List Nat) : List (List Bool) → Nat
  | [] => 0
  | w :: ws => countNatList (p w) starts + countWordStarts p starts ws

def Gcount (m : Nat) : Nat :=
  countWordStarts
    (fun w i => guardedMark w i)
    (startPositions m)
    (allWords m)

def Gev (m : Nat) : Nat :=
  countWordStarts
    (fun w i => guardedMark w i && !parityAt w i)
    (startPositions m)
    (allWords m)

def Godd (m : Nat) : Nat :=
  countWordStarts
    (fun w i => guardedMark w i && parityAt w i)
    (startPositions m)
    (allWords m)

def Hcount (m : Nat) : Nat :=
  countWordStarts
    (fun w i => guardedMark w i && fixedBlockAt w i)
    (startPositions m)
    (allWords m)

set_option maxRecDepth 1000000

theorem guarded_count_identity_6 : Gev 6 = Godd 6 + Hcount 6 := by
  rfl

theorem guarded_count_identity_7 : Gev 7 = Godd 7 + Hcount 7 := by
  rfl

theorem guarded_count_identity_8 : Gev 8 = Godd 8 + Hcount 8 := by
  rfl

theorem guarded_count_identity_9 : Gev 9 = Godd 9 + Hcount 9 := by
  rfl

theorem guarded_count_identity_10 : Gev 10 = Godd 10 + Hcount 10 := by
  rfl

theorem guarded_count_identity_11 : Gev 11 = Godd 11 + Hcount 11 := by
  rfl

theorem guarded_count_identity_12 : Gev 12 = Godd 12 + Hcount 12 := by
  rfl

theorem Gcount_6 : Gcount 6 = 21 := by
  rfl

theorem Gcount_7 : Gcount 7 = 42 := by
  rfl

theorem Gcount_8 : Gcount 8 = 105 := by
  rfl

theorem Gcount_9 : Gcount 9 = 210 := by
  rfl

theorem Gcount_10 : Gcount 10 = 420 := by
  rfl

theorem Gcount_11 : Gcount 11 = 798 := by
  rfl

theorem Gcount_12 : Gcount 12 = 1491 := by
  rfl

theorem Hcount_6 : Hcount 6 = 1 := by
  rfl

theorem Hcount_7 : Hcount 7 = 2 := by
  rfl

theorem Hcount_8 : Hcount 8 = 5 := by
  rfl

theorem Hcount_9 : Hcount 9 = 10 := by
  rfl

theorem Hcount_10 : Hcount 10 = 20 := by
  rfl

theorem Hcount_11 : Hcount 11 = 38 := by
  rfl

theorem Hcount_12 : Hcount 12 = 71 := by
  rfl

end BEDC.Derived.Window6SignedInvolutionFixedPoint
