import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompletionFunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompletionFunctorUp : Type where
  | mk (M U R Q A G E T H C P N : BHist) : CompletionFunctorUp

def completionFunctorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: completionFunctorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: completionFunctorEncodeBHist h

def completionFunctorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (completionFunctorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (completionFunctorDecodeBHist tail)

private theorem CompletionFunctorTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      completionFunctorDecodeBHist (completionFunctorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def completionFunctorToEventFlow :
    CompletionFunctorUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | CompletionFunctorUp.mk M U R Q A G E T H C P N =>
      [[BMark.b1, BMark.b0, BMark.b1],
        completionFunctorEncodeBHist M,
        completionFunctorEncodeBHist U,
        completionFunctorEncodeBHist R,
        completionFunctorEncodeBHist Q,
        completionFunctorEncodeBHist A,
        completionFunctorEncodeBHist G,
        completionFunctorEncodeBHist E,
        completionFunctorEncodeBHist T,
        completionFunctorEncodeBHist H,
        completionFunctorEncodeBHist C,
        completionFunctorEncodeBHist P,
        completionFunctorEncodeBHist N]

def completionFunctorFromEventFlow : EventFlow → Option CompletionFunctorUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag :: rest0 =>
      match rest0 with
      | [] => none
      | M :: rest1 =>
          match rest1 with
          | [] => none
          | U :: rest2 =>
              match rest2 with
              | [] => none
              | R :: rest3 =>
                  match rest3 with
                  | [] => none
                  | Q :: rest4 =>
                      match rest4 with
                      | [] => none
                      | A :: rest5 =>
                          match rest5 with
                          | [] => none
                          | G :: rest6 =>
                              match rest6 with
                              | [] => none
                              | E :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | T :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | H :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | C :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | P :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | N :: rest12 =>
                                                      match rest12 with
                                                      | [] =>
                                                          some
                                                            (CompletionFunctorUp.mk
                                                              (completionFunctorDecodeBHist M)
                                                              (completionFunctorDecodeBHist U)
                                                              (completionFunctorDecodeBHist R)
                                                              (completionFunctorDecodeBHist Q)
                                                              (completionFunctorDecodeBHist A)
                                                              (completionFunctorDecodeBHist G)
                                                              (completionFunctorDecodeBHist E)
                                                              (completionFunctorDecodeBHist T)
                                                              (completionFunctorDecodeBHist H)
                                                              (completionFunctorDecodeBHist C)
                                                              (completionFunctorDecodeBHist P)
                                                              (completionFunctorDecodeBHist N))
                                                      | _ :: _ => none

private theorem CompletionFunctorTasteGate_single_carrier_alignment_round_trip
    (x : CompletionFunctorUp) :
    completionFunctorFromEventFlow (completionFunctorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M U R Q A G E T H C P N =>
      change
        some
            (CompletionFunctorUp.mk
              (completionFunctorDecodeBHist (completionFunctorEncodeBHist M))
              (completionFunctorDecodeBHist (completionFunctorEncodeBHist U))
              (completionFunctorDecodeBHist (completionFunctorEncodeBHist R))
              (completionFunctorDecodeBHist (completionFunctorEncodeBHist Q))
              (completionFunctorDecodeBHist (completionFunctorEncodeBHist A))
              (completionFunctorDecodeBHist (completionFunctorEncodeBHist G))
              (completionFunctorDecodeBHist (completionFunctorEncodeBHist E))
              (completionFunctorDecodeBHist (completionFunctorEncodeBHist T))
              (completionFunctorDecodeBHist (completionFunctorEncodeBHist H))
              (completionFunctorDecodeBHist (completionFunctorEncodeBHist C))
              (completionFunctorDecodeBHist (completionFunctorEncodeBHist P))
              (completionFunctorDecodeBHist (completionFunctorEncodeBHist N))) =
          some (CompletionFunctorUp.mk M U R Q A G E T H C P N)
      rw [CompletionFunctorTasteGate_single_carrier_alignment_decode M,
        CompletionFunctorTasteGate_single_carrier_alignment_decode U,
        CompletionFunctorTasteGate_single_carrier_alignment_decode R,
        CompletionFunctorTasteGate_single_carrier_alignment_decode Q,
        CompletionFunctorTasteGate_single_carrier_alignment_decode A,
        CompletionFunctorTasteGate_single_carrier_alignment_decode G,
        CompletionFunctorTasteGate_single_carrier_alignment_decode E,
        CompletionFunctorTasteGate_single_carrier_alignment_decode T,
        CompletionFunctorTasteGate_single_carrier_alignment_decode H,
        CompletionFunctorTasteGate_single_carrier_alignment_decode C,
        CompletionFunctorTasteGate_single_carrier_alignment_decode P,
        CompletionFunctorTasteGate_single_carrier_alignment_decode N]

private theorem CompletionFunctorTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompletionFunctorUp} :
    completionFunctorToEventFlow x = completionFunctorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      completionFunctorFromEventFlow (completionFunctorToEventFlow x) =
        completionFunctorFromEventFlow (completionFunctorToEventFlow y) :=
    congrArg completionFunctorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompletionFunctorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompletionFunctorTasteGate_single_carrier_alignment_round_trip y)))

instance completionFunctorBHistCarrier :
    BHistCarrier CompletionFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := completionFunctorToEventFlow
  fromEventFlow := completionFunctorFromEventFlow

instance completionFunctorChapterTasteGate :
    ChapterTasteGate CompletionFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change completionFunctorFromEventFlow (completionFunctorToEventFlow x) = some x
    exact CompletionFunctorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompletionFunctorTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CompletionFunctorTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier CompletionFunctorUp) ∧
      Nonempty (ChapterTasteGate CompletionFunctorUp) ∧
        (∀ h : BHist, completionFunctorDecodeBHist (completionFunctorEncodeBHist h) = h) ∧
          (∀ x : CompletionFunctorUp,
            completionFunctorFromEventFlow (completionFunctorToEventFlow x) = some x) ∧
            (∀ x y : CompletionFunctorUp,
              completionFunctorToEventFlow x = completionFunctorToEventFlow y → x = y) ∧
              completionFunctorEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨completionFunctorBHistCarrier⟩,
      ⟨completionFunctorChapterTasteGate⟩,
      CompletionFunctorTasteGate_single_carrier_alignment_decode,
      CompletionFunctorTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CompletionFunctorTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CompletionFunctorUp
