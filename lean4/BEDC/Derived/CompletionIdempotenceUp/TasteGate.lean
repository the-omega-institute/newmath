import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompletionIdempotenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompletionIdempotenceUp : Type where
  | mk (F R Q W D G A C P N : BHist) : CompletionIdempotenceUp
  deriving DecidableEq

def completionIdempotenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: completionIdempotenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: completionIdempotenceEncodeBHist h

def completionIdempotenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (completionIdempotenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (completionIdempotenceDecodeBHist tail)

private theorem CompletionIdempotenceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      completionIdempotenceDecodeBHist (completionIdempotenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def completionIdempotenceFields : CompletionIdempotenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompletionIdempotenceUp.mk F R Q W D G A C P N =>
      [F, R, Q, W, D, G, A, C, P, N]

def completionIdempotenceToEventFlow : CompletionIdempotenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map completionIdempotenceEncodeBHist (completionIdempotenceFields x)

def completionIdempotenceFromEventFlow
    (ef : EventFlow) : Option CompletionIdempotenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match ef with
  | [] => none
  | F :: restF =>
      match restF with
      | [] => none
      | R :: restR =>
          match restR with
          | [] => none
          | Q :: restQ =>
              match restQ with
              | [] => none
              | W :: restW =>
                  match restW with
                  | [] => none
                  | D :: restD =>
                      match restD with
                      | [] => none
                      | G :: restG =>
                          match restG with
                          | [] => none
                          | A :: restA =>
                              match restA with
                              | [] => none
                              | C :: restC =>
                                  match restC with
                                  | [] => none
                                  | P :: restP =>
                                      match restP with
                                      | [] => none
                                      | N :: restN =>
                                          match restN with
                                          | [] =>
                                              some
                                                (CompletionIdempotenceUp.mk
                                                  (completionIdempotenceDecodeBHist F)
                                                  (completionIdempotenceDecodeBHist R)
                                                  (completionIdempotenceDecodeBHist Q)
                                                  (completionIdempotenceDecodeBHist W)
                                                  (completionIdempotenceDecodeBHist D)
                                                  (completionIdempotenceDecodeBHist G)
                                                  (completionIdempotenceDecodeBHist A)
                                                  (completionIdempotenceDecodeBHist C)
                                                  (completionIdempotenceDecodeBHist P)
                                                  (completionIdempotenceDecodeBHist N))
                                          | _ :: _ => none

private theorem CompletionIdempotenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompletionIdempotenceUp,
      completionIdempotenceFromEventFlow (completionIdempotenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F R Q W D G A C P N =>
      change
        some
          (CompletionIdempotenceUp.mk
            (completionIdempotenceDecodeBHist (completionIdempotenceEncodeBHist F))
            (completionIdempotenceDecodeBHist (completionIdempotenceEncodeBHist R))
            (completionIdempotenceDecodeBHist (completionIdempotenceEncodeBHist Q))
            (completionIdempotenceDecodeBHist (completionIdempotenceEncodeBHist W))
            (completionIdempotenceDecodeBHist (completionIdempotenceEncodeBHist D))
            (completionIdempotenceDecodeBHist (completionIdempotenceEncodeBHist G))
            (completionIdempotenceDecodeBHist (completionIdempotenceEncodeBHist A))
            (completionIdempotenceDecodeBHist (completionIdempotenceEncodeBHist C))
            (completionIdempotenceDecodeBHist (completionIdempotenceEncodeBHist P))
            (completionIdempotenceDecodeBHist (completionIdempotenceEncodeBHist N))) =
          some (CompletionIdempotenceUp.mk F R Q W D G A C P N)
      rw [CompletionIdempotenceTasteGate_single_carrier_alignment_decode F,
        CompletionIdempotenceTasteGate_single_carrier_alignment_decode R,
        CompletionIdempotenceTasteGate_single_carrier_alignment_decode Q,
        CompletionIdempotenceTasteGate_single_carrier_alignment_decode W,
        CompletionIdempotenceTasteGate_single_carrier_alignment_decode D,
        CompletionIdempotenceTasteGate_single_carrier_alignment_decode G,
        CompletionIdempotenceTasteGate_single_carrier_alignment_decode A,
        CompletionIdempotenceTasteGate_single_carrier_alignment_decode C,
        CompletionIdempotenceTasteGate_single_carrier_alignment_decode P,
        CompletionIdempotenceTasteGate_single_carrier_alignment_decode N]

private theorem CompletionIdempotenceTasteGate_single_carrier_alignment_injective
    {x y : CompletionIdempotenceUp} :
    completionIdempotenceToEventFlow x = completionIdempotenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      completionIdempotenceFromEventFlow (completionIdempotenceToEventFlow x) =
        completionIdempotenceFromEventFlow (completionIdempotenceToEventFlow y) :=
    congrArg completionIdempotenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompletionIdempotenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompletionIdempotenceTasteGate_single_carrier_alignment_round_trip y)))

instance completionIdempotenceBHistCarrier : BHistCarrier CompletionIdempotenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := completionIdempotenceToEventFlow
  fromEventFlow := completionIdempotenceFromEventFlow

instance completionIdempotenceChapterTasteGate :
    ChapterTasteGate CompletionIdempotenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change completionIdempotenceFromEventFlow (completionIdempotenceToEventFlow x) = some x
    exact CompletionIdempotenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompletionIdempotenceTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate CompletionIdempotenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  completionIdempotenceChapterTasteGate

theorem CompletionIdempotenceTasteGate_single_carrier_alignment :
    (forall x : CompletionIdempotenceUp,
      completionIdempotenceFromEventFlow (completionIdempotenceToEventFlow x) = some x) ∧
      (forall x y : CompletionIdempotenceUp,
        completionIdempotenceToEventFlow x = completionIdempotenceToEventFlow y -> x = y) ∧
        completionIdempotenceFields
          (CompletionIdempotenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
          [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
            BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CompletionIdempotenceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => CompletionIdempotenceTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.CompletionIdempotenceUp
