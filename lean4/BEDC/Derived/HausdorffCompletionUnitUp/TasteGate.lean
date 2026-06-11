import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HausdorffCompletionUnitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HausdorffCompletionUnitUp : Type where
  | mk (M S J W R E H C P N : BHist) : HausdorffCompletionUnitUp
  deriving DecidableEq

def hausdorffCompletionUnitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hausdorffCompletionUnitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hausdorffCompletionUnitEncodeBHist h

def hausdorffCompletionUnitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hausdorffCompletionUnitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hausdorffCompletionUnitDecodeBHist tail)

private theorem HausdorffCompletionUnitTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hausdorffCompletionUnitToEventFlow : HausdorffCompletionUnitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | HausdorffCompletionUnitUp.mk M S J W R E H C P N =>
      [hausdorffCompletionUnitEncodeBHist M,
        hausdorffCompletionUnitEncodeBHist S,
        hausdorffCompletionUnitEncodeBHist J,
        hausdorffCompletionUnitEncodeBHist W,
        hausdorffCompletionUnitEncodeBHist R,
        hausdorffCompletionUnitEncodeBHist E,
        hausdorffCompletionUnitEncodeBHist H,
        hausdorffCompletionUnitEncodeBHist C,
        hausdorffCompletionUnitEncodeBHist P,
        hausdorffCompletionUnitEncodeBHist N]

def hausdorffCompletionUnitFromEventFlow : EventFlow → Option HausdorffCompletionUnitUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | M :: rest0 =>
      match rest0 with
      | [] => none
      | S :: rest1 =>
          match rest1 with
          | [] => none
          | J :: rest2 =>
              match rest2 with
              | [] => none
              | W :: rest3 =>
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
                                                (HausdorffCompletionUnitUp.mk
                                                  (hausdorffCompletionUnitDecodeBHist M)
                                                  (hausdorffCompletionUnitDecodeBHist S)
                                                  (hausdorffCompletionUnitDecodeBHist J)
                                                  (hausdorffCompletionUnitDecodeBHist W)
                                                  (hausdorffCompletionUnitDecodeBHist R)
                                                  (hausdorffCompletionUnitDecodeBHist E)
                                                  (hausdorffCompletionUnitDecodeBHist H)
                                                  (hausdorffCompletionUnitDecodeBHist C)
                                                  (hausdorffCompletionUnitDecodeBHist P)
                                                  (hausdorffCompletionUnitDecodeBHist N))
                                          | _ :: _ => none

private theorem HausdorffCompletionUnitTasteGate_single_carrier_alignment_round_trip :
    ∀ x : HausdorffCompletionUnitUp,
      hausdorffCompletionUnitFromEventFlow (hausdorffCompletionUnitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M S J W R E H C P N =>
      change
        some
          (HausdorffCompletionUnitUp.mk
            (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEncodeBHist M))
            (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEncodeBHist S))
            (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEncodeBHist J))
            (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEncodeBHist W))
            (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEncodeBHist R))
            (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEncodeBHist E))
            (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEncodeBHist H))
            (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEncodeBHist C))
            (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEncodeBHist P))
            (hausdorffCompletionUnitDecodeBHist (hausdorffCompletionUnitEncodeBHist N))) =
          some (HausdorffCompletionUnitUp.mk M S J W R E H C P N)
      rw [HausdorffCompletionUnitTasteGate_single_carrier_alignment_decode M,
        HausdorffCompletionUnitTasteGate_single_carrier_alignment_decode S,
        HausdorffCompletionUnitTasteGate_single_carrier_alignment_decode J,
        HausdorffCompletionUnitTasteGate_single_carrier_alignment_decode W,
        HausdorffCompletionUnitTasteGate_single_carrier_alignment_decode R,
        HausdorffCompletionUnitTasteGate_single_carrier_alignment_decode E,
        HausdorffCompletionUnitTasteGate_single_carrier_alignment_decode H,
        HausdorffCompletionUnitTasteGate_single_carrier_alignment_decode C,
        HausdorffCompletionUnitTasteGate_single_carrier_alignment_decode P,
        HausdorffCompletionUnitTasteGate_single_carrier_alignment_decode N]

private theorem HausdorffCompletionUnitToEventFlow_injective
    {x y : HausdorffCompletionUnitUp} :
    hausdorffCompletionUnitToEventFlow x = hausdorffCompletionUnitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hausdorffCompletionUnitFromEventFlow (hausdorffCompletionUnitToEventFlow x) =
        hausdorffCompletionUnitFromEventFlow (hausdorffCompletionUnitToEventFlow y) :=
    congrArg hausdorffCompletionUnitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (HausdorffCompletionUnitTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (HausdorffCompletionUnitTasteGate_single_carrier_alignment_round_trip y)))

instance hausdorffCompletionUnitBHistCarrier : BHistCarrier HausdorffCompletionUnitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hausdorffCompletionUnitToEventFlow
  fromEventFlow := hausdorffCompletionUnitFromEventFlow

instance hausdorffCompletionUnitChapterTasteGate :
    ChapterTasteGate HausdorffCompletionUnitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hausdorffCompletionUnitFromEventFlow (hausdorffCompletionUnitToEventFlow x) = some x
    exact HausdorffCompletionUnitTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HausdorffCompletionUnitToEventFlow_injective heq)

theorem HausdorffCompletionUnitTasteGate_single_carrier_alignment :
    (∀ h : BHist, hausdorffCompletionUnitDecodeBHist
      (hausdorffCompletionUnitEncodeBHist h) = h) ∧
      (∀ x : HausdorffCompletionUnitUp,
        hausdorffCompletionUnitFromEventFlow
          (hausdorffCompletionUnitToEventFlow x) = some x) ∧
        hausdorffCompletionUnitEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨HausdorffCompletionUnitTasteGate_single_carrier_alignment_decode,
    HausdorffCompletionUnitTasteGate_single_carrier_alignment_round_trip, rfl⟩

end BEDC.Derived.HausdorffCompletionUnitUp
