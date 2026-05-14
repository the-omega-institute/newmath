import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedUniversalTraceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedUniversalTraceUp : Type where
  | mk (fuel substrate source ledger readback transport route provenance name : BHist) :
      BoundedUniversalTraceUp
  deriving DecidableEq

def boundedUniversalTraceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedUniversalTraceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedUniversalTraceEncodeBHist h

def boundedUniversalTraceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedUniversalTraceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedUniversalTraceDecodeBHist tail)

private theorem boundedUniversalTraceDecode_encode_bhist :
    ∀ h : BHist, boundedUniversalTraceDecodeBHist (boundedUniversalTraceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def boundedUniversalTraceToEventFlow : BoundedUniversalTraceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedUniversalTraceUp.mk fuel substrate source ledger readback transport route provenance name =>
      [[BMark.b0],
        boundedUniversalTraceEncodeBHist fuel,
        [BMark.b1, BMark.b0],
        boundedUniversalTraceEncodeBHist substrate,
        [BMark.b1, BMark.b1, BMark.b0],
        boundedUniversalTraceEncodeBHist source,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedUniversalTraceEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedUniversalTraceEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedUniversalTraceEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedUniversalTraceEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        boundedUniversalTraceEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        boundedUniversalTraceEncodeBHist name]

private def boundedUniversalTraceDecodePacket
    (fuel substrate source ledger readback transport route provenance name : RawEvent) :
    BoundedUniversalTraceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BoundedUniversalTraceUp.mk
    (boundedUniversalTraceDecodeBHist fuel)
    (boundedUniversalTraceDecodeBHist substrate)
    (boundedUniversalTraceDecodeBHist source)
    (boundedUniversalTraceDecodeBHist ledger)
    (boundedUniversalTraceDecodeBHist readback)
    (boundedUniversalTraceDecodeBHist transport)
    (boundedUniversalTraceDecodeBHist route)
    (boundedUniversalTraceDecodeBHist provenance)
    (boundedUniversalTraceDecodeBHist name)

def boundedUniversalTraceFromEventFlow : EventFlow → Option BoundedUniversalTraceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | fuel :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | substrate :: rest3 =>
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
                              | ledger :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | readback :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | route :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | name :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (boundedUniversalTraceDecodePacket
                                                                                  fuel
                                                                                  substrate
                                                                                  source ledger
                                                                                  readback
                                                                                  transport route
                                                                                  provenance name)
                                                                          | _ :: _ => none

private theorem boundedUniversalTrace_round_trip :
    ∀ x : BoundedUniversalTraceUp,
      boundedUniversalTraceFromEventFlow (boundedUniversalTraceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk fuel substrate source ledger readback transport route provenance name =>
      change
        some
            (boundedUniversalTraceDecodePacket
              (boundedUniversalTraceEncodeBHist fuel)
              (boundedUniversalTraceEncodeBHist substrate)
              (boundedUniversalTraceEncodeBHist source)
              (boundedUniversalTraceEncodeBHist ledger)
              (boundedUniversalTraceEncodeBHist readback)
              (boundedUniversalTraceEncodeBHist transport)
              (boundedUniversalTraceEncodeBHist route)
              (boundedUniversalTraceEncodeBHist provenance)
              (boundedUniversalTraceEncodeBHist name)) =
          some
            (BoundedUniversalTraceUp.mk fuel substrate source ledger readback transport route
              provenance name)
      unfold boundedUniversalTraceDecodePacket
      rw [boundedUniversalTraceDecode_encode_bhist fuel,
        boundedUniversalTraceDecode_encode_bhist substrate,
        boundedUniversalTraceDecode_encode_bhist source,
        boundedUniversalTraceDecode_encode_bhist ledger,
        boundedUniversalTraceDecode_encode_bhist readback,
        boundedUniversalTraceDecode_encode_bhist transport,
        boundedUniversalTraceDecode_encode_bhist route,
        boundedUniversalTraceDecode_encode_bhist provenance,
        boundedUniversalTraceDecode_encode_bhist name]

private theorem boundedUniversalTraceToEventFlow_injective {x y : BoundedUniversalTraceUp} :
    boundedUniversalTraceToEventFlow x = boundedUniversalTraceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundedUniversalTraceFromEventFlow (boundedUniversalTraceToEventFlow x) =
        boundedUniversalTraceFromEventFlow (boundedUniversalTraceToEventFlow y) :=
    congrArg boundedUniversalTraceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (boundedUniversalTrace_round_trip x).symm
      (Eq.trans hread (boundedUniversalTrace_round_trip y)))

instance boundedUniversalTraceBHistCarrier : BHistCarrier BoundedUniversalTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedUniversalTraceToEventFlow
  fromEventFlow := boundedUniversalTraceFromEventFlow

instance boundedUniversalTraceChapterTasteGate : ChapterTasteGate BoundedUniversalTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change boundedUniversalTraceFromEventFlow (boundedUniversalTraceToEventFlow x) = some x
    exact boundedUniversalTrace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (boundedUniversalTraceToEventFlow_injective heq)

instance boundedUniversalTraceFieldFaithful : FieldFaithful BoundedUniversalTraceUp where
  fields := fun x =>
    match x with
    | BoundedUniversalTraceUp.mk fuel substrate source ledger readback transport route provenance
        name =>
        [fuel, substrate, source, ledger, readback, transport, route, provenance, name]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk fuel₁ substrate₁ source₁ ledger₁ readback₁ transport₁ route₁ provenance₁ name₁ =>
        cases y with
        | mk fuel₂ substrate₂ source₂ ledger₂ readback₂ transport₂ route₂ provenance₂ name₂ =>
            injection h with hFuel hTail₁
            injection hTail₁ with hSubstrate hTail₂
            injection hTail₂ with hSource hTail₃
            injection hTail₃ with hLedger hTail₄
            injection hTail₄ with hReadback hTail₅
            injection hTail₅ with hTransport hTail₆
            injection hTail₆ with hRoute hTail₇
            injection hTail₇ with hProvenance hTail₈
            injection hTail₈ with hName _
            subst hFuel
            subst hSubstrate
            subst hSource
            subst hLedger
            subst hReadback
            subst hTransport
            subst hRoute
            subst hProvenance
            subst hName
            rfl

instance boundedUniversalTraceNontrivial : Nontrivial BoundedUniversalTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BoundedUniversalTraceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BoundedUniversalTraceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BoundedUniversalTraceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  boundedUniversalTraceChapterTasteGate

theorem BoundedUniversalTraceTasteGate_single_carrier_alignment :
    (∀ h : BHist, boundedUniversalTraceDecodeBHist (boundedUniversalTraceEncodeBHist h) = h) ∧
      (∀ x : BoundedUniversalTraceUp,
        boundedUniversalTraceFromEventFlow (boundedUniversalTraceToEventFlow x) = some x) ∧
        (∀ x y : BoundedUniversalTraceUp,
          boundedUniversalTraceToEventFlow x = boundedUniversalTraceToEventFlow y → x = y) ∧
          boundedUniversalTraceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact boundedUniversalTraceDecode_encode_bhist
  · constructor
    · exact boundedUniversalTrace_round_trip
    · constructor
      · intro x y heq
        exact boundedUniversalTraceToEventFlow_injective heq
      · rfl

end BEDC.Derived.BoundedUniversalTraceUp
