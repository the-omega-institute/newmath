import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PropextTransportBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PropextTransportBoundaryUp : Type where
  | mk :
      (bidirectional direction replacement transport continuation provenance localName : BHist) →
        PropextTransportBoundaryUp
  deriving DecidableEq

def propextTransportBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: propextTransportBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: propextTransportBoundaryEncodeBHist h

def propextTransportBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (propextTransportBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (propextTransportBoundaryDecodeBHist tail)

private theorem PropextTransportBoundaryTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      propextTransportBoundaryDecodeBHist
        (propextTransportBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def propextTransportBoundaryFields : PropextTransportBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PropextTransportBoundaryUp.mk bidirectional direction replacement transport continuation
      provenance localName =>
        [bidirectional, direction, replacement, transport, continuation, provenance, localName]

def propextTransportBoundaryToEventFlow : PropextTransportBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (propextTransportBoundaryFields x).map propextTransportBoundaryEncodeBHist

def propextTransportBoundaryFromEventFlow : EventFlow → Option PropextTransportBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | bidirectional :: restBidirectional =>
      match restBidirectional with
      | direction :: restDirection =>
          match restDirection with
          | replacement :: restReplacement =>
              match restReplacement with
              | transport :: restTransport =>
                  match restTransport with
                  | continuation :: restContinuation =>
                      match restContinuation with
                      | provenance :: restProvenance =>
                          match restProvenance with
                          | localName :: rest =>
                              match rest with
                              | [] =>
                                  some
                                    (PropextTransportBoundaryUp.mk
                                      (propextTransportBoundaryDecodeBHist bidirectional)
                                      (propextTransportBoundaryDecodeBHist direction)
                                      (propextTransportBoundaryDecodeBHist replacement)
                                      (propextTransportBoundaryDecodeBHist transport)
                                      (propextTransportBoundaryDecodeBHist continuation)
                                      (propextTransportBoundaryDecodeBHist provenance)
                                      (propextTransportBoundaryDecodeBHist localName))
                              | _ :: _ => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none

private theorem propextTransportBoundary_mk_congr
    {B B' D D' R R' H H' C C' P P' N N' : BHist}
    (hB : B' = B) (hD : D' = D) (hR : R' = R) (hH : H' = H)
    (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    PropextTransportBoundaryUp.mk B' D' R' H' C' P' N' =
      PropextTransportBoundaryUp.mk B D R H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hB
  cases hD
  cases hR
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem PropextTransportBoundaryTasteGate_single_carrier_alignment_round_trip :
    ∀ x : PropextTransportBoundaryUp,
      propextTransportBoundaryFromEventFlow
        (propextTransportBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk bidirectional direction replacement transport continuation provenance localName =>
      exact
        congrArg some
          (propextTransportBoundary_mk_congr
            (PropextTransportBoundaryTasteGate_single_carrier_alignment_decode bidirectional)
            (PropextTransportBoundaryTasteGate_single_carrier_alignment_decode direction)
            (PropextTransportBoundaryTasteGate_single_carrier_alignment_decode replacement)
            (PropextTransportBoundaryTasteGate_single_carrier_alignment_decode transport)
            (PropextTransportBoundaryTasteGate_single_carrier_alignment_decode continuation)
            (PropextTransportBoundaryTasteGate_single_carrier_alignment_decode provenance)
            (PropextTransportBoundaryTasteGate_single_carrier_alignment_decode localName))

private theorem propextTransportBoundaryToEventFlow_injective
    {x y : PropextTransportBoundaryUp} :
    propextTransportBoundaryToEventFlow x = propextTransportBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      propextTransportBoundaryFromEventFlow (propextTransportBoundaryToEventFlow x) =
        propextTransportBoundaryFromEventFlow (propextTransportBoundaryToEventFlow y) :=
    congrArg propextTransportBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (PropextTransportBoundaryTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (PropextTransportBoundaryTasteGate_single_carrier_alignment_round_trip y)))

private theorem propextTransportBoundary_field_faithful :
    ∀ x y : PropextTransportBoundaryUp,
      propextTransportBoundaryFields x = propextTransportBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk bidirectional direction replacement transport continuation provenance localName =>
      cases y with
      | mk bidirectional' direction' replacement' transport' continuation' provenance'
          localName' =>
            cases hfields
            rfl

instance propextTransportBoundaryBHistCarrier : BHistCarrier PropextTransportBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := propextTransportBoundaryToEventFlow
  fromEventFlow := propextTransportBoundaryFromEventFlow

instance propextTransportBoundaryChapterTasteGate :
    ChapterTasteGate PropextTransportBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      propextTransportBoundaryFromEventFlow (propextTransportBoundaryToEventFlow x) = some x
    exact PropextTransportBoundaryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (propextTransportBoundaryToEventFlow_injective heq)

instance propextTransportBoundaryFieldFaithful : FieldFaithful PropextTransportBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := propextTransportBoundaryFields
  field_faithful := propextTransportBoundary_field_faithful

instance propextTransportBoundaryNontrivial :
    BEDC.Meta.TasteGate.Nontrivial PropextTransportBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PropextTransportBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      PropextTransportBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PropextTransportBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  propextTransportBoundaryChapterTasteGate

theorem PropextTransportBoundaryTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate PropextTransportBoundaryUp) ∧
      Nonempty (FieldFaithful PropextTransportBoundaryUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial PropextTransportBoundaryUp) ∧
      (∀ h : BHist,
        propextTransportBoundaryDecodeBHist (propextTransportBoundaryEncodeBHist h) = h) ∧
      propextTransportBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨propextTransportBoundaryChapterTasteGate⟩
  constructor
  · exact ⟨propextTransportBoundaryFieldFaithful⟩
  constructor
  · exact ⟨propextTransportBoundaryNontrivial⟩
  constructor
  · exact PropextTransportBoundaryTasteGate_single_carrier_alignment_decode
  · rfl

end BEDC.Derived.PropextTransportBoundaryUp
