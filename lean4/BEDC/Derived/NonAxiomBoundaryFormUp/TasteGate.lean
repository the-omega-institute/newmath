import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NonAxiomBoundaryFormUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NonAxiomBoundaryFormUp : Type where
  | mk :
      (boundary kind source gate transport route provenance nameRow : BHist) →
      NonAxiomBoundaryFormUp
  deriving DecidableEq

private def nonAxiomBoundaryFormEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: nonAxiomBoundaryFormEncodeBHist h
  | BHist.e1 h => BMark.b1 :: nonAxiomBoundaryFormEncodeBHist h

private def nonAxiomBoundaryFormDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (nonAxiomBoundaryFormDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (nonAxiomBoundaryFormDecodeBHist tail)

private theorem nonAxiomBoundaryFormDecode_encode_bhist :
    ∀ h : BHist,
      nonAxiomBoundaryFormDecodeBHist (nonAxiomBoundaryFormEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def nonAxiomBoundaryFormToEventFlow : NonAxiomBoundaryFormUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | NonAxiomBoundaryFormUp.mk boundary kind source gate transport route provenance nameRow =>
      [[BMark.b0],
        nonAxiomBoundaryFormEncodeBHist boundary,
        [BMark.b1, BMark.b0],
        nonAxiomBoundaryFormEncodeBHist kind,
        [BMark.b1, BMark.b1, BMark.b0],
        nonAxiomBoundaryFormEncodeBHist source,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        nonAxiomBoundaryFormEncodeBHist gate,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        nonAxiomBoundaryFormEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        nonAxiomBoundaryFormEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        nonAxiomBoundaryFormEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        nonAxiomBoundaryFormEncodeBHist nameRow]

private def nonAxiomBoundaryFormFromEventFlow : EventFlow → Option NonAxiomBoundaryFormUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | boundary :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | kind :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | source :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | gate :: rest7 =>
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
                                                                        (NonAxiomBoundaryFormUp.mk
                                                                          (nonAxiomBoundaryFormDecodeBHist
                                                                            boundary)
                                                                          (nonAxiomBoundaryFormDecodeBHist
                                                                            kind)
                                                                          (nonAxiomBoundaryFormDecodeBHist
                                                                            source)
                                                                          (nonAxiomBoundaryFormDecodeBHist
                                                                            gate)
                                                                          (nonAxiomBoundaryFormDecodeBHist
                                                                            transport)
                                                                          (nonAxiomBoundaryFormDecodeBHist
                                                                            route)
                                                                          (nonAxiomBoundaryFormDecodeBHist
                                                                            provenance)
                                                                          (nonAxiomBoundaryFormDecodeBHist
                                                                            nameRow))
                                                                  | _ :: _ => none

private theorem nonAxiomBoundaryForm_round_trip :
    ∀ x : NonAxiomBoundaryFormUp,
      nonAxiomBoundaryFormFromEventFlow (nonAxiomBoundaryFormToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk boundary kind source gate transport route provenance nameRow =>
      change
        some
          (NonAxiomBoundaryFormUp.mk
            (nonAxiomBoundaryFormDecodeBHist (nonAxiomBoundaryFormEncodeBHist boundary))
            (nonAxiomBoundaryFormDecodeBHist (nonAxiomBoundaryFormEncodeBHist kind))
            (nonAxiomBoundaryFormDecodeBHist (nonAxiomBoundaryFormEncodeBHist source))
            (nonAxiomBoundaryFormDecodeBHist (nonAxiomBoundaryFormEncodeBHist gate))
            (nonAxiomBoundaryFormDecodeBHist (nonAxiomBoundaryFormEncodeBHist transport))
            (nonAxiomBoundaryFormDecodeBHist (nonAxiomBoundaryFormEncodeBHist route))
            (nonAxiomBoundaryFormDecodeBHist (nonAxiomBoundaryFormEncodeBHist provenance))
            (nonAxiomBoundaryFormDecodeBHist (nonAxiomBoundaryFormEncodeBHist nameRow))) =
          some
            (NonAxiomBoundaryFormUp.mk boundary kind source gate transport route provenance
              nameRow)
      rw [nonAxiomBoundaryFormDecode_encode_bhist boundary,
        nonAxiomBoundaryFormDecode_encode_bhist kind,
        nonAxiomBoundaryFormDecode_encode_bhist source,
        nonAxiomBoundaryFormDecode_encode_bhist gate,
        nonAxiomBoundaryFormDecode_encode_bhist transport,
        nonAxiomBoundaryFormDecode_encode_bhist route,
        nonAxiomBoundaryFormDecode_encode_bhist provenance,
        nonAxiomBoundaryFormDecode_encode_bhist nameRow]

private theorem nonAxiomBoundaryFormToEventFlow_injective {x y : NonAxiomBoundaryFormUp} :
    nonAxiomBoundaryFormToEventFlow x = nonAxiomBoundaryFormToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      nonAxiomBoundaryFormFromEventFlow (nonAxiomBoundaryFormToEventFlow x) =
        nonAxiomBoundaryFormFromEventFlow (nonAxiomBoundaryFormToEventFlow y) :=
    congrArg nonAxiomBoundaryFormFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (nonAxiomBoundaryForm_round_trip x).symm
      (Eq.trans hread (nonAxiomBoundaryForm_round_trip y)))

instance nonAxiomBoundaryFormBHistCarrier : BHistCarrier NonAxiomBoundaryFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := nonAxiomBoundaryFormToEventFlow
  fromEventFlow := nonAxiomBoundaryFormFromEventFlow

def nonAxiomBoundaryFormTasteGate : ChapterTasteGate NonAxiomBoundaryFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change nonAxiomBoundaryFormFromEventFlow (nonAxiomBoundaryFormToEventFlow x) = some x
    exact nonAxiomBoundaryForm_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (nonAxiomBoundaryFormToEventFlow_injective heq)

def taste_gate : ChapterTasteGate NonAxiomBoundaryFormUp :=
  -- BEDC touchpoint anchor: BHist BMark
  nonAxiomBoundaryFormTasteGate

instance nonAxiomBoundaryFormChapterTasteGate : ChapterTasteGate NonAxiomBoundaryFormUp :=
  -- BEDC touchpoint anchor: BHist BMark
  nonAxiomBoundaryFormTasteGate

instance nonAxiomBoundaryFormFieldFaithful : FieldFaithful NonAxiomBoundaryFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | NonAxiomBoundaryFormUp.mk boundary kind source gate transport route provenance nameRow =>
        [boundary, kind, source, gate, transport, route, provenance, nameRow]
  field_faithful := by
    intro x y h
    cases x with
    | mk boundary1 kind1 source1 gate1 transport1 route1 provenance1 nameRow1 =>
        cases y with
        | mk boundary2 kind2 source2 gate2 transport2 route2 provenance2 nameRow2 =>
            injection h with hBoundary t1
            injection t1 with hKind t2
            injection t2 with hSource t3
            injection t3 with hGate t4
            injection t4 with hTransport t5
            injection t5 with hRoute t6
            injection t6 with hProvenance t7
            injection t7 with hNameRow _
            cases hBoundary
            cases hKind
            cases hSource
            cases hGate
            cases hTransport
            cases hRoute
            cases hProvenance
            cases hNameRow
            rfl

end BEDC.Derived.NonAxiomBoundaryFormUp
