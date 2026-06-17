import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SummationByPartsUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SummationByPartsUp : Type where
  | mk (S A Delta P B T R D E H C Q N : BHist) : SummationByPartsUp
  deriving DecidableEq

def summationByPartsEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: summationByPartsEncodeBHist h
  | BHist.e1 h => BMark.b1 :: summationByPartsEncodeBHist h

def summationByPartsDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (summationByPartsDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (summationByPartsDecodeBHist tail)

private theorem summationByParts_decode_encode :
    forall h : BHist, summationByPartsDecodeBHist (summationByPartsEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def summationByPartsToEventFlow : SummationByPartsUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SummationByPartsUp.mk S A Delta P B T R D E H C Q N =>
      [summationByPartsEncodeBHist S, summationByPartsEncodeBHist A,
        summationByPartsEncodeBHist Delta, summationByPartsEncodeBHist P,
        summationByPartsEncodeBHist B, summationByPartsEncodeBHist T,
        summationByPartsEncodeBHist R, summationByPartsEncodeBHist D,
        summationByPartsEncodeBHist E, summationByPartsEncodeBHist H,
        summationByPartsEncodeBHist C, summationByPartsEncodeBHist Q,
        summationByPartsEncodeBHist N]

def summationByPartsFromEventFlow : EventFlow -> Option SummationByPartsUp
  -- BEDC touchpoint anchor: BHist BMark
  | S :: restS =>
      match restS with
      | A :: restA =>
          match restA with
          | Delta :: restDelta =>
              match restDelta with
              | P :: restP =>
                  match restP with
                  | B :: restB =>
                      match restB with
                      | T :: restT =>
                          match restT with
                          | R :: restR =>
                              match restR with
                              | D :: restD =>
                                  match restD with
                                  | E :: restE =>
                                      match restE with
                                      | H :: restH =>
                                          match restH with
                                          | C :: restC =>
                                              match restC with
                                              | Q :: restQ =>
                                                  match restQ with
                                                  | N :: restN =>
                                                      match restN with
                                                      | [] =>
                                                          some
                                                            (SummationByPartsUp.mk
                                                              (summationByPartsDecodeBHist S)
                                                              (summationByPartsDecodeBHist A)
                                                              (summationByPartsDecodeBHist Delta)
                                                              (summationByPartsDecodeBHist P)
                                                              (summationByPartsDecodeBHist B)
                                                              (summationByPartsDecodeBHist T)
                                                              (summationByPartsDecodeBHist R)
                                                              (summationByPartsDecodeBHist D)
                                                              (summationByPartsDecodeBHist E)
                                                              (summationByPartsDecodeBHist H)
                                                              (summationByPartsDecodeBHist C)
                                                              (summationByPartsDecodeBHist Q)
                                                              (summationByPartsDecodeBHist N))
                                                      | _ :: _ => none
                                                  | [] => none
                                              | [] => none
                                          | [] => none
                                      | [] => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem summationByParts_round_trip :
    forall x : SummationByPartsUp,
      summationByPartsFromEventFlow (summationByPartsToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S A Delta P B T R D E H C Q N =>
      rw [summationByPartsToEventFlow, summationByPartsFromEventFlow,
        summationByParts_decode_encode S, summationByParts_decode_encode A,
        summationByParts_decode_encode Delta, summationByParts_decode_encode P,
        summationByParts_decode_encode B, summationByParts_decode_encode T,
        summationByParts_decode_encode R, summationByParts_decode_encode D,
        summationByParts_decode_encode E, summationByParts_decode_encode H,
        summationByParts_decode_encode C, summationByParts_decode_encode Q,
        summationByParts_decode_encode N]

private theorem summationByPartsToEventFlow_injective {x y : SummationByPartsUp} :
    summationByPartsToEventFlow x = summationByPartsToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      summationByPartsFromEventFlow (summationByPartsToEventFlow x) =
        summationByPartsFromEventFlow (summationByPartsToEventFlow y) :=
    congrArg summationByPartsFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (summationByParts_round_trip x).symm
      (Eq.trans hread (summationByParts_round_trip y)))

instance summationByPartsBHistCarrier : BHistCarrier SummationByPartsUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := summationByPartsToEventFlow
  fromEventFlow := summationByPartsFromEventFlow

instance summationByPartsChapterTasteGate : ChapterTasteGate SummationByPartsUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change summationByPartsFromEventFlow (summationByPartsToEventFlow x) = some x
    exact summationByParts_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (summationByPartsToEventFlow_injective heq)

def taste_gate : ChapterTasteGate SummationByPartsUp :=
  -- BEDC touchpoint anchor: BHist BMark
  summationByPartsChapterTasteGate

theorem SummationByPartsTasteGate_single_carrier_alignment :
    (forall h : BHist, summationByPartsDecodeBHist (summationByPartsEncodeBHist h) = h) ∧
      (forall x : SummationByPartsUp,
        summationByPartsFromEventFlow (summationByPartsToEventFlow x) = some x) ∧
      (forall x y : SummationByPartsUp,
        summationByPartsToEventFlow x = summationByPartsToEventFlow y -> x = y) ∧
      summationByPartsEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨summationByParts_decode_encode, summationByParts_round_trip,
      fun _ _ heq => summationByPartsToEventFlow_injective heq, rfl⟩

end BEDC.Derived.SummationByPartsUp
