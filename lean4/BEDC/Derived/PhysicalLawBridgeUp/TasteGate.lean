import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PhysicalLawBridgeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PhysicalLawBridgeUp : Type where
  | mk :
      (law empirical bridge object openFit failure transport route provenance localName : BHist) →
        PhysicalLawBridgeUp
  deriving DecidableEq

def physicalLawBridgeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: physicalLawBridgeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: physicalLawBridgeEncodeBHist h

def physicalLawBridgeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (physicalLawBridgeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (physicalLawBridgeDecodeBHist tail)

private theorem physicalLawBridgeDecode_encode_bhist :
    ∀ h : BHist, physicalLawBridgeDecodeBHist (physicalLawBridgeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def physicalLawBridgeFields : PhysicalLawBridgeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PhysicalLawBridgeUp.mk law empirical bridge object openFit failure transport route
      provenance localName =>
      [law, empirical, bridge, object, openFit, failure, transport, route, provenance,
        localName]

def physicalLawBridgeToEventFlow : PhysicalLawBridgeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (physicalLawBridgeFields x).map physicalLawBridgeEncodeBHist

def physicalLawBridgeFromEventFlow : EventFlow → Option PhysicalLawBridgeUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | law :: rest0 =>
      match rest0 with
      | [] => none
      | empirical :: rest1 =>
          match rest1 with
          | [] => none
          | bridge :: rest2 =>
              match rest2 with
              | [] => none
              | object :: rest3 =>
                  match rest3 with
                  | [] => none
                  | openFit :: rest4 =>
                      match rest4 with
                      | [] => none
                      | failure :: rest5 =>
                          match rest5 with
                          | [] => none
                          | transport :: rest6 =>
                              match rest6 with
                              | [] => none
                              | route :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | provenance :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | localName :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (PhysicalLawBridgeUp.mk
                                                  (physicalLawBridgeDecodeBHist law)
                                                  (physicalLawBridgeDecodeBHist empirical)
                                                  (physicalLawBridgeDecodeBHist bridge)
                                                  (physicalLawBridgeDecodeBHist object)
                                                  (physicalLawBridgeDecodeBHist openFit)
                                                  (physicalLawBridgeDecodeBHist failure)
                                                  (physicalLawBridgeDecodeBHist transport)
                                                  (physicalLawBridgeDecodeBHist route)
                                                  (physicalLawBridgeDecodeBHist provenance)
                                                  (physicalLawBridgeDecodeBHist localName))
                                          | _ :: _ => none

private theorem physicalLawBridge_round_trip :
    ∀ x : PhysicalLawBridgeUp,
      physicalLawBridgeFromEventFlow (physicalLawBridgeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk law empirical bridge object openFit failure transport route provenance localName =>
      change
        some
          (PhysicalLawBridgeUp.mk
            (physicalLawBridgeDecodeBHist (physicalLawBridgeEncodeBHist law))
            (physicalLawBridgeDecodeBHist (physicalLawBridgeEncodeBHist empirical))
            (physicalLawBridgeDecodeBHist (physicalLawBridgeEncodeBHist bridge))
            (physicalLawBridgeDecodeBHist (physicalLawBridgeEncodeBHist object))
            (physicalLawBridgeDecodeBHist (physicalLawBridgeEncodeBHist openFit))
            (physicalLawBridgeDecodeBHist (physicalLawBridgeEncodeBHist failure))
            (physicalLawBridgeDecodeBHist (physicalLawBridgeEncodeBHist transport))
            (physicalLawBridgeDecodeBHist (physicalLawBridgeEncodeBHist route))
            (physicalLawBridgeDecodeBHist (physicalLawBridgeEncodeBHist provenance))
            (physicalLawBridgeDecodeBHist (physicalLawBridgeEncodeBHist localName))) =
          some
            (PhysicalLawBridgeUp.mk law empirical bridge object openFit failure transport route
              provenance localName)
      rw [physicalLawBridgeDecode_encode_bhist law,
        physicalLawBridgeDecode_encode_bhist empirical,
        physicalLawBridgeDecode_encode_bhist bridge,
        physicalLawBridgeDecode_encode_bhist object,
        physicalLawBridgeDecode_encode_bhist openFit,
        physicalLawBridgeDecode_encode_bhist failure,
        physicalLawBridgeDecode_encode_bhist transport,
        physicalLawBridgeDecode_encode_bhist route,
        physicalLawBridgeDecode_encode_bhist provenance,
        physicalLawBridgeDecode_encode_bhist localName]

private theorem physicalLawBridgeToEventFlow_injective {x y : PhysicalLawBridgeUp} :
    physicalLawBridgeToEventFlow x = physicalLawBridgeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      physicalLawBridgeFromEventFlow (physicalLawBridgeToEventFlow x) =
        physicalLawBridgeFromEventFlow (physicalLawBridgeToEventFlow y) :=
    congrArg physicalLawBridgeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (physicalLawBridge_round_trip x).symm
      (Eq.trans hread (physicalLawBridge_round_trip y)))

private theorem physicalLawBridge_field_faithful :
    ∀ x y : PhysicalLawBridgeUp,
      physicalLawBridgeFields x = physicalLawBridgeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk law₁ empirical₁ bridge₁ object₁ openFit₁ failure₁ transport₁ route₁
      provenance₁ localName₁ =>
      cases y with
      | mk law₂ empirical₂ bridge₂ object₂ openFit₂ failure₂ transport₂ route₂
          provenance₂ localName₂ =>
          injection h with hLaw tail1
          injection tail1 with hEmpirical tail2
          injection tail2 with hBridge tail3
          injection tail3 with hObject tail4
          injection tail4 with hOpenFit tail5
          injection tail5 with hFailure tail6
          injection tail6 with hTransport tail7
          injection tail7 with hRoute tail8
          injection tail8 with hProvenance tail9
          injection tail9 with hLocalName _
          cases hLaw
          cases hEmpirical
          cases hBridge
          cases hObject
          cases hOpenFit
          cases hFailure
          cases hTransport
          cases hRoute
          cases hProvenance
          cases hLocalName
          rfl

instance physicalLawBridgeBHistCarrier : BHistCarrier PhysicalLawBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := physicalLawBridgeToEventFlow
  fromEventFlow := physicalLawBridgeFromEventFlow

instance physicalLawBridgeChapterTasteGate :
    ChapterTasteGate PhysicalLawBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change physicalLawBridgeFromEventFlow (physicalLawBridgeToEventFlow x) = some x
    exact physicalLawBridge_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (physicalLawBridgeToEventFlow_injective heq)

instance physicalLawBridgeFieldFaithful : FieldFaithful PhysicalLawBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := physicalLawBridgeFields
  field_faithful := physicalLawBridge_field_faithful

instance physicalLawBridgeNontrivial : Nontrivial PhysicalLawBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PhysicalLawBridgeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PhysicalLawBridgeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PhysicalLawBridgeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  physicalLawBridgeChapterTasteGate

theorem PhysicalLawBridgeTasteGate_single_carrier_alignment :
    (∀ h : BHist, physicalLawBridgeDecodeBHist (physicalLawBridgeEncodeBHist h) = h) ∧
      (∀ x : PhysicalLawBridgeUp,
        physicalLawBridgeFromEventFlow (physicalLawBridgeToEventFlow x) = some x) ∧
        (∀ x y : PhysicalLawBridgeUp,
          physicalLawBridgeToEventFlow x = physicalLawBridgeToEventFlow y → x = y) ∧
          physicalLawBridgeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact physicalLawBridgeDecode_encode_bhist
  · constructor
    · exact physicalLawBridge_round_trip
    · constructor
      · intro x y heq
        exact physicalLawBridgeToEventFlow_injective heq
      · rfl

end BEDC.Derived.PhysicalLawBridgeUp
