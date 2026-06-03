import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchySpaceMorphismUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchySpaceMorphismUp : Type where
  | mk (S T A W D H C P N : BHist) : RegularCauchySpaceMorphismUp
  deriving DecidableEq

def regularCauchySpaceMorphismEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchySpaceMorphismEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchySpaceMorphismEncodeBHist h

def regularCauchySpaceMorphismDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchySpaceMorphismDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchySpaceMorphismDecodeBHist tail)

private theorem RegularCauchySpaceMorphismTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      regularCauchySpaceMorphismDecodeBHist (regularCauchySpaceMorphismEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchySpaceMorphismToEventFlow : RegularCauchySpaceMorphismUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchySpaceMorphismUp.mk S T A W D H C P N =>
      [regularCauchySpaceMorphismEncodeBHist S, regularCauchySpaceMorphismEncodeBHist T,
        regularCauchySpaceMorphismEncodeBHist A, regularCauchySpaceMorphismEncodeBHist W,
        regularCauchySpaceMorphismEncodeBHist D, regularCauchySpaceMorphismEncodeBHist H,
        regularCauchySpaceMorphismEncodeBHist C, regularCauchySpaceMorphismEncodeBHist P,
        regularCauchySpaceMorphismEncodeBHist N]

def regularCauchySpaceMorphismFromEventFlow :
    EventFlow → Option RegularCauchySpaceMorphismUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match flow with
      | [] => none
      | S :: rest0 =>
          match rest0 with
          | [] => none
          | T :: rest1 =>
              match rest1 with
              | [] => none
              | A :: rest2 =>
                  match rest2 with
                  | [] => none
                  | W :: rest3 =>
                      match rest3 with
                      | [] => none
                      | D :: rest4 =>
                          match rest4 with
                          | [] => none
                          | H :: rest5 =>
                              match rest5 with
                              | [] => none
                              | C :: rest6 =>
                                  match rest6 with
                                  | [] => none
                                  | P :: rest7 =>
                                      match rest7 with
                                      | [] => none
                                      | N :: rest8 =>
                                          match rest8 with
                                          | [] =>
                                              some
                                                (RegularCauchySpaceMorphismUp.mk
                                                  (regularCauchySpaceMorphismDecodeBHist S)
                                                  (regularCauchySpaceMorphismDecodeBHist T)
                                                  (regularCauchySpaceMorphismDecodeBHist A)
                                                  (regularCauchySpaceMorphismDecodeBHist W)
                                                  (regularCauchySpaceMorphismDecodeBHist D)
                                                  (regularCauchySpaceMorphismDecodeBHist H)
                                                  (regularCauchySpaceMorphismDecodeBHist C)
                                                  (regularCauchySpaceMorphismDecodeBHist P)
                                                  (regularCauchySpaceMorphismDecodeBHist N))
                                          | _ :: _ => none

private theorem RegularCauchySpaceMorphismTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchySpaceMorphismUp,
      regularCauchySpaceMorphismFromEventFlow (regularCauchySpaceMorphismToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S T A W D H C P N =>
      change
        some
          (RegularCauchySpaceMorphismUp.mk
            (regularCauchySpaceMorphismDecodeBHist
              (regularCauchySpaceMorphismEncodeBHist S))
            (regularCauchySpaceMorphismDecodeBHist
              (regularCauchySpaceMorphismEncodeBHist T))
            (regularCauchySpaceMorphismDecodeBHist
              (regularCauchySpaceMorphismEncodeBHist A))
            (regularCauchySpaceMorphismDecodeBHist
              (regularCauchySpaceMorphismEncodeBHist W))
            (regularCauchySpaceMorphismDecodeBHist
              (regularCauchySpaceMorphismEncodeBHist D))
            (regularCauchySpaceMorphismDecodeBHist
              (regularCauchySpaceMorphismEncodeBHist H))
            (regularCauchySpaceMorphismDecodeBHist
              (regularCauchySpaceMorphismEncodeBHist C))
            (regularCauchySpaceMorphismDecodeBHist
              (regularCauchySpaceMorphismEncodeBHist P))
            (regularCauchySpaceMorphismDecodeBHist
              (regularCauchySpaceMorphismEncodeBHist N))) =
          some (RegularCauchySpaceMorphismUp.mk S T A W D H C P N)
      rw [RegularCauchySpaceMorphismTasteGate_single_carrier_alignment_decode_encode S,
        RegularCauchySpaceMorphismTasteGate_single_carrier_alignment_decode_encode T,
        RegularCauchySpaceMorphismTasteGate_single_carrier_alignment_decode_encode A,
        RegularCauchySpaceMorphismTasteGate_single_carrier_alignment_decode_encode W,
        RegularCauchySpaceMorphismTasteGate_single_carrier_alignment_decode_encode D,
        RegularCauchySpaceMorphismTasteGate_single_carrier_alignment_decode_encode H,
        RegularCauchySpaceMorphismTasteGate_single_carrier_alignment_decode_encode C,
        RegularCauchySpaceMorphismTasteGate_single_carrier_alignment_decode_encode P,
        RegularCauchySpaceMorphismTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularCauchySpaceMorphismTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchySpaceMorphismUp} :
    regularCauchySpaceMorphismToEventFlow x =
      regularCauchySpaceMorphismToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchySpaceMorphismFromEventFlow (regularCauchySpaceMorphismToEventFlow x) =
        regularCauchySpaceMorphismFromEventFlow (regularCauchySpaceMorphismToEventFlow y) :=
    congrArg regularCauchySpaceMorphismFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RegularCauchySpaceMorphismTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchySpaceMorphismTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchySpaceMorphismBHistCarrier :
    BHistCarrier RegularCauchySpaceMorphismUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchySpaceMorphismToEventFlow
  fromEventFlow := regularCauchySpaceMorphismFromEventFlow

instance regularCauchySpaceMorphismChapterTasteGate :
    ChapterTasteGate RegularCauchySpaceMorphismUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchySpaceMorphismFromEventFlow
      (regularCauchySpaceMorphismToEventFlow x) = some x
    exact RegularCauchySpaceMorphismTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchySpaceMorphismTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchySpaceMorphismUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchySpaceMorphismChapterTasteGate

theorem RegularCauchySpaceMorphismTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchySpaceMorphismDecodeBHist (regularCauchySpaceMorphismEncodeBHist h) = h) ∧
      (∀ x : RegularCauchySpaceMorphismUp,
        regularCauchySpaceMorphismFromEventFlow
          (regularCauchySpaceMorphismToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchySpaceMorphismUp,
          regularCauchySpaceMorphismToEventFlow x =
            regularCauchySpaceMorphismToEventFlow y → x = y) ∧
          regularCauchySpaceMorphismEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RegularCauchySpaceMorphismTasteGate_single_carrier_alignment_decode_encode,
      RegularCauchySpaceMorphismTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RegularCauchySpaceMorphismTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchySpaceMorphismUp
