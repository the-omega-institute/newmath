import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchySubsequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchySubsequenceUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (S T W R E H C P N : BHist) : RegularCauchySubsequenceUp
  deriving DecidableEq

def regularCauchySubsequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchySubsequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchySubsequenceEncodeBHist h

def regularCauchySubsequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchySubsequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchySubsequenceDecodeBHist tail)

private theorem regularCauchySubsequenceDecode_encode_bhist :
    ∀ h : BHist,
      regularCauchySubsequenceDecodeBHist
          (regularCauchySubsequenceEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchySubsequenceFields : RegularCauchySubsequenceUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | RegularCauchySubsequenceUp.mk S T W R E H C P N =>
      [S, T, W, R, E, H, C, P, N]

def regularCauchySubsequenceToEventFlow :
    RegularCauchySubsequenceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | RegularCauchySubsequenceUp.mk S T W R E H C P N =>
      [regularCauchySubsequenceEncodeBHist S,
        regularCauchySubsequenceEncodeBHist T,
        regularCauchySubsequenceEncodeBHist W,
        regularCauchySubsequenceEncodeBHist R,
        regularCauchySubsequenceEncodeBHist E,
        regularCauchySubsequenceEncodeBHist H,
        regularCauchySubsequenceEncodeBHist C,
        regularCauchySubsequenceEncodeBHist P,
        regularCauchySubsequenceEncodeBHist N]

def regularCauchySubsequenceFromEventFlow :
    EventFlow → Option RegularCauchySubsequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | S :: T :: W :: R :: E :: H :: C :: P :: N :: [] =>
      some
        (RegularCauchySubsequenceUp.mk
          (regularCauchySubsequenceDecodeBHist S)
          (regularCauchySubsequenceDecodeBHist T)
          (regularCauchySubsequenceDecodeBHist W)
          (regularCauchySubsequenceDecodeBHist R)
          (regularCauchySubsequenceDecodeBHist E)
          (regularCauchySubsequenceDecodeBHist H)
          (regularCauchySubsequenceDecodeBHist C)
          (regularCauchySubsequenceDecodeBHist P)
          (regularCauchySubsequenceDecodeBHist N))
  | _ => none

private theorem regularCauchySubsequence_round_trip :
    ∀ x : RegularCauchySubsequenceUp,
      regularCauchySubsequenceFromEventFlow
          (regularCauchySubsequenceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S T W R E H C P N =>
      simp only [regularCauchySubsequenceToEventFlow,
        regularCauchySubsequenceFromEventFlow,
        regularCauchySubsequenceDecode_encode_bhist]

private theorem regularCauchySubsequenceToEventFlow_injective
    {x y : RegularCauchySubsequenceUp} :
    regularCauchySubsequenceToEventFlow x =
        regularCauchySubsequenceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          regularCauchySubsequenceFromEventFlow
            (regularCauchySubsequenceToEventFlow x) :=
        (regularCauchySubsequence_round_trip x).symm
      _ =
          regularCauchySubsequenceFromEventFlow
            (regularCauchySubsequenceToEventFlow y) :=
        congrArg regularCauchySubsequenceFromEventFlow hxy
      _ = some y := regularCauchySubsequence_round_trip y
  exact Option.some.inj optionEq

theorem RegularCauchySubsequenceUp_carrier_alignment
    (G : RegularCauchySubsequenceUp) :
    ∃ S T W R E H C P N : BHist,
      G = RegularCauchySubsequenceUp.mk S T W R E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases G with
  | mk S T W R E H C P N =>
      exact ⟨S, T, W, R, E, H, C, P, N, rfl⟩

instance regularCauchySubsequenceBHistCarrier :
    BHistCarrier RegularCauchySubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchySubsequenceToEventFlow
  fromEventFlow := regularCauchySubsequenceFromEventFlow

instance regularCauchySubsequenceChapterTasteGate :
    ChapterTasteGate RegularCauchySubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchySubsequenceFromEventFlow
          (regularCauchySubsequenceToEventFlow x) =
        some x
    exact regularCauchySubsequence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchySubsequenceToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchySubsequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchySubsequenceChapterTasteGate

end BEDC.Derived.RegularCauchySubsequenceUp
