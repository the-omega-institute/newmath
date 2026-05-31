import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyCofinalSubsequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyCofinalSubsequenceUp : Type where
  | mk (S W phi D R E H C P N : BHist) : RegularCauchyCofinalSubsequenceUp
  deriving DecidableEq

def regularCauchyCofinalSubsequenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyCofinalSubsequenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyCofinalSubsequenceEncodeBHist h

def regularCauchyCofinalSubsequenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyCofinalSubsequenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyCofinalSubsequenceDecodeBHist tail)

private theorem regularCauchyCofinalSubsequenceDecode_encode_bhist :
    ∀ h : BHist,
      regularCauchyCofinalSubsequenceDecodeBHist
          (regularCauchyCofinalSubsequenceEncodeBHist h) =
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

def regularCauchyCofinalSubsequenceToEventFlow :
    RegularCauchyCofinalSubsequenceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | RegularCauchyCofinalSubsequenceUp.mk S W phi D R E H C P N =>
      [regularCauchyCofinalSubsequenceEncodeBHist S,
        regularCauchyCofinalSubsequenceEncodeBHist W,
        regularCauchyCofinalSubsequenceEncodeBHist phi,
        regularCauchyCofinalSubsequenceEncodeBHist D,
        regularCauchyCofinalSubsequenceEncodeBHist R,
        regularCauchyCofinalSubsequenceEncodeBHist E,
        regularCauchyCofinalSubsequenceEncodeBHist H,
        regularCauchyCofinalSubsequenceEncodeBHist C,
        regularCauchyCofinalSubsequenceEncodeBHist P,
        regularCauchyCofinalSubsequenceEncodeBHist N]

def regularCauchyCofinalSubsequenceFromEventFlow :
    EventFlow → Option RegularCauchyCofinalSubsequenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: rest0 =>
      match rest0 with
      | [] => none
      | W :: rest1 =>
          match rest1 with
          | [] => none
          | phi :: rest2 =>
              match rest2 with
              | [] => none
              | D :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R :: rest4 =>
                      match rest4 with
                      | [] => none
                      | E :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                              | C :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | P :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | N :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (RegularCauchyCofinalSubsequenceUp.mk
                                                  (regularCauchyCofinalSubsequenceDecodeBHist S)
                                                  (regularCauchyCofinalSubsequenceDecodeBHist W)
                                                  (regularCauchyCofinalSubsequenceDecodeBHist phi)
                                                  (regularCauchyCofinalSubsequenceDecodeBHist D)
                                                  (regularCauchyCofinalSubsequenceDecodeBHist R)
                                                  (regularCauchyCofinalSubsequenceDecodeBHist E)
                                                  (regularCauchyCofinalSubsequenceDecodeBHist H)
                                                  (regularCauchyCofinalSubsequenceDecodeBHist C)
                                                  (regularCauchyCofinalSubsequenceDecodeBHist P)
                                                  (regularCauchyCofinalSubsequenceDecodeBHist N))
                                          | _ :: _ => none

private theorem regularCauchyCofinalSubsequence_round_trip :
    ∀ x : RegularCauchyCofinalSubsequenceUp,
      regularCauchyCofinalSubsequenceFromEventFlow
          (regularCauchyCofinalSubsequenceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S W phi D R E H C P N =>
      change
        some
          (RegularCauchyCofinalSubsequenceUp.mk
            (regularCauchyCofinalSubsequenceDecodeBHist
              (regularCauchyCofinalSubsequenceEncodeBHist S))
            (regularCauchyCofinalSubsequenceDecodeBHist
              (regularCauchyCofinalSubsequenceEncodeBHist W))
            (regularCauchyCofinalSubsequenceDecodeBHist
              (regularCauchyCofinalSubsequenceEncodeBHist phi))
            (regularCauchyCofinalSubsequenceDecodeBHist
              (regularCauchyCofinalSubsequenceEncodeBHist D))
            (regularCauchyCofinalSubsequenceDecodeBHist
              (regularCauchyCofinalSubsequenceEncodeBHist R))
            (regularCauchyCofinalSubsequenceDecodeBHist
              (regularCauchyCofinalSubsequenceEncodeBHist E))
            (regularCauchyCofinalSubsequenceDecodeBHist
              (regularCauchyCofinalSubsequenceEncodeBHist H))
            (regularCauchyCofinalSubsequenceDecodeBHist
              (regularCauchyCofinalSubsequenceEncodeBHist C))
            (regularCauchyCofinalSubsequenceDecodeBHist
              (regularCauchyCofinalSubsequenceEncodeBHist P))
            (regularCauchyCofinalSubsequenceDecodeBHist
              (regularCauchyCofinalSubsequenceEncodeBHist N))) =
          some (RegularCauchyCofinalSubsequenceUp.mk S W phi D R E H C P N)
      rw [regularCauchyCofinalSubsequenceDecode_encode_bhist S,
        regularCauchyCofinalSubsequenceDecode_encode_bhist W,
        regularCauchyCofinalSubsequenceDecode_encode_bhist phi,
        regularCauchyCofinalSubsequenceDecode_encode_bhist D,
        regularCauchyCofinalSubsequenceDecode_encode_bhist R,
        regularCauchyCofinalSubsequenceDecode_encode_bhist E,
        regularCauchyCofinalSubsequenceDecode_encode_bhist H,
        regularCauchyCofinalSubsequenceDecode_encode_bhist C,
        regularCauchyCofinalSubsequenceDecode_encode_bhist P,
        regularCauchyCofinalSubsequenceDecode_encode_bhist N]

private theorem regularCauchyCofinalSubsequenceToEventFlow_injective
    {x y : RegularCauchyCofinalSubsequenceUp} :
    regularCauchyCofinalSubsequenceToEventFlow x =
        regularCauchyCofinalSubsequenceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          regularCauchyCofinalSubsequenceFromEventFlow
            (regularCauchyCofinalSubsequenceToEventFlow x) :=
        (regularCauchyCofinalSubsequence_round_trip x).symm
      _ =
          regularCauchyCofinalSubsequenceFromEventFlow
            (regularCauchyCofinalSubsequenceToEventFlow y) :=
        congrArg regularCauchyCofinalSubsequenceFromEventFlow hxy
      _ = some y := regularCauchyCofinalSubsequence_round_trip y
  exact Option.some.inj optionEq

instance regularCauchyCofinalSubsequenceBHistCarrier :
    BHistCarrier RegularCauchyCofinalSubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyCofinalSubsequenceToEventFlow
  fromEventFlow := regularCauchyCofinalSubsequenceFromEventFlow

instance regularCauchyCofinalSubsequenceChapterTasteGate :
    ChapterTasteGate RegularCauchyCofinalSubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyCofinalSubsequenceFromEventFlow
          (regularCauchyCofinalSubsequenceToEventFlow x) =
        some x
    exact regularCauchyCofinalSubsequence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyCofinalSubsequenceToEventFlow_injective heq)

theorem RegularCauchyCofinalSubsequenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        regularCauchyCofinalSubsequenceDecodeBHist
            (regularCauchyCofinalSubsequenceEncodeBHist h) =
          h) ∧
      (∀ x : RegularCauchyCofinalSubsequenceUp,
        regularCauchyCofinalSubsequenceFromEventFlow
            (regularCauchyCofinalSubsequenceToEventFlow x) =
          some x) ∧
        (∀ x y : RegularCauchyCofinalSubsequenceUp,
          regularCauchyCofinalSubsequenceToEventFlow x =
              regularCauchyCofinalSubsequenceToEventFlow y →
            x = y) ∧
          regularCauchyCofinalSubsequenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact regularCauchyCofinalSubsequenceDecode_encode_bhist
  · constructor
    · exact regularCauchyCofinalSubsequence_round_trip
    · constructor
      · intro x y heq
        exact regularCauchyCofinalSubsequenceToEventFlow_injective heq
      · rfl

end BEDC.Derived.RegularCauchyCofinalSubsequenceUp
