import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ExternalSupplyFailureWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ExternalSupplyFailureWitnessUp : Type where
  | mk :
      (boundary request failed diagnostic target gate transport route provenance name : BHist) →
        ExternalSupplyFailureWitnessUp
  deriving DecidableEq

def externalSupplyFailureWitnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: externalSupplyFailureWitnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: externalSupplyFailureWitnessEncodeBHist h

def externalSupplyFailureWitnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (externalSupplyFailureWitnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (externalSupplyFailureWitnessDecodeBHist tail)

private theorem externalSupplyFailureWitnessDecode_encode_bhist :
    ∀ h : BHist,
      externalSupplyFailureWitnessDecodeBHist
          (externalSupplyFailureWitnessEncodeBHist h) =
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

def externalSupplyFailureWitnessFields :
    ExternalSupplyFailureWitnessUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | ExternalSupplyFailureWitnessUp.mk boundary request failed diagnostic target gate
      transport route provenance name =>
      [boundary, request, failed, diagnostic, target, gate, transport, route,
        provenance, name]

def externalSupplyFailureWitnessToEventFlow :
    ExternalSupplyFailureWitnessUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | ExternalSupplyFailureWitnessUp.mk boundary request failed diagnostic target gate
      transport route provenance name =>
      [[BMark.b1, BMark.b1, BMark.b0],
        [BMark.b0, BMark.b1, BMark.b1],
        [BMark.b1, BMark.b0, BMark.b0],
        externalSupplyFailureWitnessEncodeBHist boundary,
        externalSupplyFailureWitnessEncodeBHist request,
        externalSupplyFailureWitnessEncodeBHist failed,
        externalSupplyFailureWitnessEncodeBHist diagnostic,
        externalSupplyFailureWitnessEncodeBHist target,
        externalSupplyFailureWitnessEncodeBHist gate,
        externalSupplyFailureWitnessEncodeBHist transport,
        externalSupplyFailureWitnessEncodeBHist route,
        externalSupplyFailureWitnessEncodeBHist provenance,
        externalSupplyFailureWitnessEncodeBHist name]

def externalSupplyFailureWitnessFromEventFlow :
    EventFlow → Option ExternalSupplyFailureWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | _tag0 :: _tag1 :: _tag2 :: boundary :: request :: failed :: diagnostic ::
      target :: gate :: transport :: route :: provenance :: name :: [] =>
      some
        (ExternalSupplyFailureWitnessUp.mk
          (externalSupplyFailureWitnessDecodeBHist boundary)
          (externalSupplyFailureWitnessDecodeBHist request)
          (externalSupplyFailureWitnessDecodeBHist failed)
          (externalSupplyFailureWitnessDecodeBHist diagnostic)
          (externalSupplyFailureWitnessDecodeBHist target)
          (externalSupplyFailureWitnessDecodeBHist gate)
          (externalSupplyFailureWitnessDecodeBHist transport)
          (externalSupplyFailureWitnessDecodeBHist route)
          (externalSupplyFailureWitnessDecodeBHist provenance)
          (externalSupplyFailureWitnessDecodeBHist name))
  | _ => none

private theorem externalSupplyFailureWitness_round_trip :
    ∀ x : ExternalSupplyFailureWitnessUp,
      externalSupplyFailureWitnessFromEventFlow
          (externalSupplyFailureWitnessToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk boundary request failed diagnostic target gate transport route provenance name =>
      simp only [externalSupplyFailureWitnessToEventFlow,
        externalSupplyFailureWitnessFromEventFlow,
        externalSupplyFailureWitnessDecode_encode_bhist]

private theorem externalSupplyFailureWitnessToEventFlow_injective
    {x y : ExternalSupplyFailureWitnessUp} :
    externalSupplyFailureWitnessToEventFlow x =
        externalSupplyFailureWitnessToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          externalSupplyFailureWitnessFromEventFlow
            (externalSupplyFailureWitnessToEventFlow x) :=
        (externalSupplyFailureWitness_round_trip x).symm
      _ =
          externalSupplyFailureWitnessFromEventFlow
            (externalSupplyFailureWitnessToEventFlow y) :=
        congrArg externalSupplyFailureWitnessFromEventFlow hxy
      _ = some y := externalSupplyFailureWitness_round_trip y
  exact Option.some.inj optionEq

instance externalSupplyFailureWitnessBHistCarrier :
    BHistCarrier ExternalSupplyFailureWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := externalSupplyFailureWitnessToEventFlow
  fromEventFlow := externalSupplyFailureWitnessFromEventFlow

instance externalSupplyFailureWitnessChapterTasteGate :
    ChapterTasteGate ExternalSupplyFailureWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      externalSupplyFailureWitnessFromEventFlow
          (externalSupplyFailureWitnessToEventFlow x) =
        some x
    exact externalSupplyFailureWitness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (externalSupplyFailureWitnessToEventFlow_injective heq)

def taste_gate : ChapterTasteGate ExternalSupplyFailureWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  externalSupplyFailureWitnessChapterTasteGate

instance externalSupplyFailureWitnessFieldFaithful :
    FieldFaithful ExternalSupplyFailureWitnessUp where
  fields := externalSupplyFailureWitnessFields
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk boundary1 request1 failed1 diagnostic1 target1 gate1 transport1 route1
        provenance1 name1 =>
        cases y with
        | mk boundary2 request2 failed2 diagnostic2 target2 gate2 transport2 route2
            provenance2 name2 =>
            injection h with hBoundary t1
            injection t1 with hRequest t2
            injection t2 with hFailed t3
            injection t3 with hDiagnostic t4
            injection t4 with hTarget t5
            injection t5 with hGate t6
            injection t6 with hTransport t7
            injection t7 with hRoute t8
            injection t8 with hProvenance t9
            injection t9 with hName _
            cases hBoundary
            cases hRequest
            cases hFailed
            cases hDiagnostic
            cases hTarget
            cases hGate
            cases hTransport
            cases hRoute
            cases hProvenance
            cases hName
            rfl

instance externalSupplyFailureWitnessNontrivial :
    Nontrivial ExternalSupplyFailureWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ExternalSupplyFailureWitnessUp.mk
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ExternalSupplyFailureWitnessUp.mk
        (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

end BEDC.Derived.ExternalSupplyFailureWitnessUp
