namespace BEDC.Derived.Window6MirrorSkewNeutralSplit

/-!
Finite Window6 skew/neutral mirror decomposition for the RH bridge
no-neutral-leak obligation.  This is a finite residual-surface certificate,
not a proof of RH.
-/

structure Word6 where
  b0 : Bool
  b1 : Bool
  b2 : Bool
  b3 : Bool
  b4 : Bool
  b5 : Bool

def word6 (b0 b1 b2 b3 b4 b5 : Bool) : Word6 :=
  ⟨b0, b1, b2, b3, b4, b5⟩

def noAdj : List Bool → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => !(a && b) && noAdj (b :: rest)

def noAdj6 (b0 b1 b2 b3 b4 b5 : Bool) : Bool :=
  !(b0 && b1) && !(b1 && b2) && !(b2 && b3) && !(b3 && b4) && !(b4 && b5)

def noAdjWord (w : Word6) : Bool :=
  noAdj6 w.b0 w.b1 w.b2 w.b3 w.b4 w.b5

def mirror6 (b0 b1 b2 b3 b4 b5 : Bool) : Word6 :=
  word6 b5 b4 b3 b2 b1 b0

def mirrorWord (w : Word6) : Word6 :=
  mirror6 w.b0 w.b1 w.b2 w.b3 w.b4 w.b5

def palindrome6 (b0 b1 b2 b3 b4 b5 : Bool) : Bool :=
  (b0 == b5) && (b1 == b4) && (b2 == b3)

def palindromeWord (w : Word6) : Bool :=
  palindrome6 w.b0 w.b1 w.b2 w.b3 w.b4 w.b5

theorem mirror6_involutive
    (b0 b1 b2 b3 b4 b5 : Bool) :
    mirrorWord (mirror6 b0 b1 b2 b3 b4 b5) = word6 b0 b1 b2 b3 b4 b5 := by
  rfl

theorem mirrorWord_involutive (w : Word6) :
    mirrorWord (mirrorWord w) = w := by
  cases w
  rfl

theorem mirror6_preserves_noAdj
    (b0 b1 b2 b3 b4 b5 : Bool)
    (h : noAdj6 b0 b1 b2 b3 b4 b5 = true) :
    noAdjWord (mirror6 b0 b1 b2 b3 b4 b5) = true := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;>
    unfold noAdj6 at h <;>
    unfold noAdjWord mirror6 word6 noAdj6 <;>
    cases h <;>
    rfl

theorem mirror6_fixed_iff_palindrome
    (b0 b1 b2 b3 b4 b5 : Bool) :
    mirror6 b0 b1 b2 b3 b4 b5 = word6 b0 b1 b2 b3 b4 b5 ↔
      palindrome6 b0 b1 b2 b3 b4 b5 = true := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;>
    unfold mirror6 word6 palindrome6 <;>
    constructor <;>
    intro h <;>
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

def bitNat : Bool → Nat
  | false => 0
  | true => 1

def natLtBool : Nat → Nat → Bool
  | 0, 0 => false
  | 0, _ + 1 => true
  | _ + 1, 0 => false
  | m + 1, n + 1 => natLtBool m n

def mirrorList6 (w : List Bool) : List Bool :=
  [bitAt w 5, bitAt w 4, bitAt w 3, bitAt w 2, bitAt w 1, bitAt w 0]

def palindromeList6 (w : List Bool) : Bool :=
  (bitAt w 0 == bitAt w 5) &&
    (bitAt w 1 == bitAt w 4) &&
    (bitAt w 2 == bitAt w 3)

def code6 (w : List Bool) : Nat :=
  bitNat (bitAt w 0) * 32 +
    bitNat (bitAt w 1) * 16 +
    bitNat (bitAt w 2) * 8 +
    bitNat (bitAt w 3) * 4 +
    bitNat (bitAt w 4) * 2 +
    bitNat (bitAt w 5)

def countWords (p : List Bool → Bool) : List (List Bool) → Nat
  | [] => 0
  | w :: ws => (if p w then 1 else 0) + countWords p ws

def window6Words : List (List Bool) :=
  allWords 6

def window6Member (w : List Bool) : Bool :=
  noAdj w

def neutralWord (w : List Bool) : Bool :=
  noAdj w && palindromeList6 w

def skewPairRepresentative (w : List Bool) : Bool :=
  noAdj w &&
    !(palindromeList6 w) &&
    natLtBool (code6 w) (code6 (mirrorList6 w))

def window6Count : Nat :=
  countWords window6Member window6Words

def neutralCount : Nat :=
  countWords neutralWord window6Words

def skewPairCount : Nat :=
  countWords skewPairRepresentative window6Words

theorem window6_count : window6Count = 21 := by
  rfl

theorem neutral_count : neutralCount = 3 := by
  rfl

theorem skew_pair_count : skewPairCount = 9 := by
  rfl

theorem window6_mirror_skew_neutral_split_certificate :
    window6Count = neutralCount + 2 * skewPairCount := by
  rfl

theorem mirror6_100100_value :
    mirror6 true false false true false false =
      word6 false false true false false true := by
  rfl

theorem mirror6_010010_fixed :
    mirror6 false true false false true false =
      word6 false true false false true false := by
  rfl

theorem palindrome6_010010 :
    palindrome6 false true false false true false = true := by
  rfl

theorem noAdj6_010010 :
    noAdj6 false true false false true false = true := by
  rfl

theorem mirror6_preserves_noAdj_100100 :
    noAdjWord (mirror6 true false false true false false) = true := by
  rfl

theorem neutral_fixed_000000 :
    mirror6 false false false false false false =
      word6 false false false false false false := by
  rfl

theorem neutral_fixed_100001 :
    mirror6 true false false false false true =
      word6 true false false false false true := by
  rfl

end BEDC.Derived.Window6MirrorSkewNeutralSplit
