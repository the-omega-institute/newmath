import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocalStencilObservationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocalStencilObservationUp : Type where
  | mk (stencil rule observedWindow classifier transport route provenance nameRow : BHist) :
      LocalStencilObservationUp
  deriving DecidableEq

def localStencilObservationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: localStencilObservationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: localStencilObservationEncodeBHist h

def localStencilObservationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (localStencilObservationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (localStencilObservationDecodeBHist tail)

private theorem localStencilObservationDecode_encode_bhist :
    ∀ h : BHist, localStencilObservationDecodeBHist
      (localStencilObservationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def localStencilObservationToEventFlow : LocalStencilObservationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LocalStencilObservationUp.mk stencil rule observedWindow classifier transport route
      provenance nameRow =>
      [[BMark.b0],
        localStencilObservationEncodeBHist stencil,
        [BMark.b1, BMark.b0],
        localStencilObservationEncodeBHist rule,
        [BMark.b1, BMark.b1, BMark.b0],
        localStencilObservationEncodeBHist observedWindow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        localStencilObservationEncodeBHist classifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        localStencilObservationEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        localStencilObservationEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        localStencilObservationEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        localStencilObservationEncodeBHist nameRow]

def localStencilObservationFromEventFlow : EventFlow → Option LocalStencilObservationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | stencil :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | rule :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | observedWindow :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | classifier :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | route :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | provenance :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | nameRow :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (LocalStencilObservationUp.mk
                                                                          (localStencilObservationDecodeBHist
                                                                            stencil)
                                                                          (localStencilObservationDecodeBHist
                                                                            rule)
                                                                          (localStencilObservationDecodeBHist
                                                                            observedWindow)
                                                                          (localStencilObservationDecodeBHist
                                                                            classifier)
                                                                          (localStencilObservationDecodeBHist
                                                                            transport)
                                                                          (localStencilObservationDecodeBHist
                                                                            route)
                                                                          (localStencilObservationDecodeBHist
                                                                            provenance)
                                                                          (localStencilObservationDecodeBHist
                                                                            nameRow))
                                                                  | _ :: _ => none

private theorem localStencilObservation_round_trip :
    ∀ x : LocalStencilObservationUp,
      localStencilObservationFromEventFlow (localStencilObservationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk stencil rule observedWindow classifier transport route provenance nameRow =>
      change
        some
          (LocalStencilObservationUp.mk
            (localStencilObservationDecodeBHist (localStencilObservationEncodeBHist stencil))
            (localStencilObservationDecodeBHist (localStencilObservationEncodeBHist rule))
            (localStencilObservationDecodeBHist
              (localStencilObservationEncodeBHist observedWindow))
            (localStencilObservationDecodeBHist
              (localStencilObservationEncodeBHist classifier))
            (localStencilObservationDecodeBHist (localStencilObservationEncodeBHist transport))
            (localStencilObservationDecodeBHist (localStencilObservationEncodeBHist route))
            (localStencilObservationDecodeBHist (localStencilObservationEncodeBHist provenance))
            (localStencilObservationDecodeBHist (localStencilObservationEncodeBHist nameRow))) =
          some
            (LocalStencilObservationUp.mk stencil rule observedWindow classifier transport route
              provenance nameRow)
      rw [localStencilObservationDecode_encode_bhist stencil,
        localStencilObservationDecode_encode_bhist rule,
        localStencilObservationDecode_encode_bhist observedWindow,
        localStencilObservationDecode_encode_bhist classifier,
        localStencilObservationDecode_encode_bhist transport,
        localStencilObservationDecode_encode_bhist route,
        localStencilObservationDecode_encode_bhist provenance,
        localStencilObservationDecode_encode_bhist nameRow]

private theorem localStencilObservationToEventFlow_injective {x y : LocalStencilObservationUp} :
    localStencilObservationToEventFlow x = localStencilObservationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      localStencilObservationFromEventFlow (localStencilObservationToEventFlow x) =
        localStencilObservationFromEventFlow (localStencilObservationToEventFlow y) :=
    congrArg localStencilObservationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (localStencilObservation_round_trip x).symm
      (Eq.trans hread (localStencilObservation_round_trip y)))

instance localStencilObservationBHistCarrier : BHistCarrier LocalStencilObservationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := localStencilObservationToEventFlow
  fromEventFlow := localStencilObservationFromEventFlow

instance localStencilObservationChapterTasteGate :
    ChapterTasteGate LocalStencilObservationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change localStencilObservationFromEventFlow (localStencilObservationToEventFlow x) = some x
    exact localStencilObservation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (localStencilObservationToEventFlow_injective heq)

instance localStencilObservationFieldFaithful : FieldFaithful LocalStencilObservationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | LocalStencilObservationUp.mk stencil rule observedWindow classifier transport route
        provenance nameRow =>
        [stencil, rule, observedWindow, classifier, transport, route, provenance, nameRow]
  field_faithful := by
    intro x y h
    cases x with
    | mk stencil₁ rule₁ observedWindow₁ classifier₁ transport₁ route₁ provenance₁ nameRow₁ =>
        cases y with
        | mk stencil₂ rule₂ observedWindow₂ classifier₂ transport₂ route₂ provenance₂ nameRow₂ =>
            simp only [] at h
            cases h
            rfl

end BEDC.Derived.LocalStencilObservationUp
