import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyTailSubsequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyTailSubsequenceUp : Type where
  | mk (S W k D R E H C P N : BHist) : RegularCauchyTailSubsequenceUp
  deriving DecidableEq

def regularCauchyTailSubsequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyTailSubsequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyTailSubsequenceEncodeBHist h

def regularCauchyTailSubsequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyTailSubsequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyTailSubsequenceDecodeBHist tail)

private theorem regularCauchyTailSubsequence_decode_encode_bhist :
    ∀ h : BHist,
      regularCauchyTailSubsequenceDecodeBHist
        (regularCauchyTailSubsequenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyTailSubsequenceFields :
    RegularCauchyTailSubsequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyTailSubsequenceUp.mk S W k D R E H C P N => [S, W, k, D, R, E, H, C, P, N]

def regularCauchyTailSubsequenceToEventFlow :
    RegularCauchyTailSubsequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyTailSubsequenceFields x).map regularCauchyTailSubsequenceEncodeBHist

private def regularCauchyTailSubsequenceRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => regularCauchyTailSubsequenceRawAt n rest

private def regularCauchyTailSubsequenceLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => regularCauchyTailSubsequenceLengthEq n rest

def regularCauchyTailSubsequenceFromEventFlow :
    EventFlow → Option RegularCauchyTailSubsequenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match regularCauchyTailSubsequenceLengthEq 10 flow with
      | true =>
          some
            (RegularCauchyTailSubsequenceUp.mk
              (regularCauchyTailSubsequenceDecodeBHist
                (regularCauchyTailSubsequenceRawAt 0 flow))
              (regularCauchyTailSubsequenceDecodeBHist
                (regularCauchyTailSubsequenceRawAt 1 flow))
              (regularCauchyTailSubsequenceDecodeBHist
                (regularCauchyTailSubsequenceRawAt 2 flow))
              (regularCauchyTailSubsequenceDecodeBHist
                (regularCauchyTailSubsequenceRawAt 3 flow))
              (regularCauchyTailSubsequenceDecodeBHist
                (regularCauchyTailSubsequenceRawAt 4 flow))
              (regularCauchyTailSubsequenceDecodeBHist
                (regularCauchyTailSubsequenceRawAt 5 flow))
              (regularCauchyTailSubsequenceDecodeBHist
                (regularCauchyTailSubsequenceRawAt 6 flow))
              (regularCauchyTailSubsequenceDecodeBHist
                (regularCauchyTailSubsequenceRawAt 7 flow))
              (regularCauchyTailSubsequenceDecodeBHist
                (regularCauchyTailSubsequenceRawAt 8 flow))
              (regularCauchyTailSubsequenceDecodeBHist
                (regularCauchyTailSubsequenceRawAt 9 flow)))
      | false => none

private theorem regularCauchyTailSubsequence_round_trip :
    ∀ x : RegularCauchyTailSubsequenceUp,
      regularCauchyTailSubsequenceFromEventFlow
          (regularCauchyTailSubsequenceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S W k D R E H C P N =>
      change
        some
          (RegularCauchyTailSubsequenceUp.mk
            (regularCauchyTailSubsequenceDecodeBHist
              (regularCauchyTailSubsequenceEncodeBHist S))
            (regularCauchyTailSubsequenceDecodeBHist
              (regularCauchyTailSubsequenceEncodeBHist W))
            (regularCauchyTailSubsequenceDecodeBHist
              (regularCauchyTailSubsequenceEncodeBHist k))
            (regularCauchyTailSubsequenceDecodeBHist
              (regularCauchyTailSubsequenceEncodeBHist D))
            (regularCauchyTailSubsequenceDecodeBHist
              (regularCauchyTailSubsequenceEncodeBHist R))
            (regularCauchyTailSubsequenceDecodeBHist
              (regularCauchyTailSubsequenceEncodeBHist E))
            (regularCauchyTailSubsequenceDecodeBHist
              (regularCauchyTailSubsequenceEncodeBHist H))
            (regularCauchyTailSubsequenceDecodeBHist
              (regularCauchyTailSubsequenceEncodeBHist C))
            (regularCauchyTailSubsequenceDecodeBHist
              (regularCauchyTailSubsequenceEncodeBHist P))
            (regularCauchyTailSubsequenceDecodeBHist
              (regularCauchyTailSubsequenceEncodeBHist N))) =
          some (RegularCauchyTailSubsequenceUp.mk S W k D R E H C P N)
      rw [regularCauchyTailSubsequence_decode_encode_bhist S,
        regularCauchyTailSubsequence_decode_encode_bhist W,
        regularCauchyTailSubsequence_decode_encode_bhist k,
        regularCauchyTailSubsequence_decode_encode_bhist D,
        regularCauchyTailSubsequence_decode_encode_bhist R,
        regularCauchyTailSubsequence_decode_encode_bhist E,
        regularCauchyTailSubsequence_decode_encode_bhist H,
        regularCauchyTailSubsequence_decode_encode_bhist C,
        regularCauchyTailSubsequence_decode_encode_bhist P,
        regularCauchyTailSubsequence_decode_encode_bhist N]

private theorem regularCauchyTailSubsequenceToEventFlow_injective
    {x y : RegularCauchyTailSubsequenceUp} :
    regularCauchyTailSubsequenceToEventFlow x =
        regularCauchyTailSubsequenceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyTailSubsequenceFromEventFlow
          (regularCauchyTailSubsequenceToEventFlow x) =
        regularCauchyTailSubsequenceFromEventFlow
          (regularCauchyTailSubsequenceToEventFlow y) :=
    congrArg regularCauchyTailSubsequenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyTailSubsequence_round_trip x).symm
      (Eq.trans hread (regularCauchyTailSubsequence_round_trip y)))

instance regularCauchyTailSubsequenceBHistCarrier :
    BHistCarrier RegularCauchyTailSubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyTailSubsequenceToEventFlow
  fromEventFlow := regularCauchyTailSubsequenceFromEventFlow

instance regularCauchyTailSubsequenceChapterTasteGate :
    ChapterTasteGate RegularCauchyTailSubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyTailSubsequenceFromEventFlow
          (regularCauchyTailSubsequenceToEventFlow x) =
        some x
    exact regularCauchyTailSubsequence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyTailSubsequenceToEventFlow_injective heq)

theorem RegularCauchyTailSubsequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyTailSubsequenceDecodeBHist
          (regularCauchyTailSubsequenceEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier RegularCauchyTailSubsequenceUp) ∧
        Nonempty (ChapterTasteGate RegularCauchyTailSubsequenceUp) ∧
          regularCauchyTailSubsequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨regularCauchyTailSubsequence_decode_encode_bhist,
      ⟨regularCauchyTailSubsequenceBHistCarrier⟩,
      ⟨regularCauchyTailSubsequenceChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RegularCauchyTailSubsequenceUp
