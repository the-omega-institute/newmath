import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteRelationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteRelationUp : Type where
  | mk
      (leftSurface rightSurface relationRows membership domainSupport rangeSupport transport
        replay provenance localName : BHist) : FiniteRelationUp
  deriving DecidableEq

def finiteRelationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteRelationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteRelationEncodeBHist h

def finiteRelationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteRelationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteRelationDecodeBHist tail)

private theorem FiniteRelationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, finiteRelationDecodeBHist (finiteRelationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteRelationFields : FiniteRelationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteRelationUp.mk leftSurface rightSurface relationRows membership domainSupport
      rangeSupport transport replay provenance localName =>
      [leftSurface, rightSurface, relationRows, membership, domainSupport, rangeSupport,
        transport, replay, provenance, localName]

def finiteRelationToEventFlow : FiniteRelationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteRelationFields x).map finiteRelationEncodeBHist

def finiteRelationFromEventFlow : EventFlow → Option FiniteRelationUp
  -- BEDC touchpoint anchor: BHist BMark
  | leftSurface :: restLeft =>
      match restLeft with
      | rightSurface :: restRight =>
          match restRight with
          | relationRows :: restRows =>
              match restRows with
              | membership :: restMembership =>
                  match restMembership with
                  | domainSupport :: restDomain =>
                      match restDomain with
                      | rangeSupport :: restRange =>
                          match restRange with
                          | transport :: restTransport =>
                              match restTransport with
                              | replay :: restReplay =>
                                  match restReplay with
                                  | provenance :: restProvenance =>
                                      match restProvenance with
                                      | localName :: rest =>
                                          match rest with
                                          | [] =>
                                              some
                                                (FiniteRelationUp.mk
                                                  (finiteRelationDecodeBHist leftSurface)
                                                  (finiteRelationDecodeBHist rightSurface)
                                                  (finiteRelationDecodeBHist relationRows)
                                                  (finiteRelationDecodeBHist membership)
                                                  (finiteRelationDecodeBHist domainSupport)
                                                  (finiteRelationDecodeBHist rangeSupport)
                                                  (finiteRelationDecodeBHist transport)
                                                  (finiteRelationDecodeBHist replay)
                                                  (finiteRelationDecodeBHist provenance)
                                                  (finiteRelationDecodeBHist localName))
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

private theorem finiteRelation_mk_congr
    {leftSurface leftSurface' rightSurface rightSurface' relationRows relationRows'
      membership membership' domainSupport domainSupport' rangeSupport rangeSupport'
      transport transport' replay replay' provenance provenance' localName localName' : BHist}
    (hLeft : leftSurface' = leftSurface) (hRight : rightSurface' = rightSurface)
    (hRows : relationRows' = relationRows) (hMember : membership' = membership)
    (hDomain : domainSupport' = domainSupport) (hRange : rangeSupport' = rangeSupport)
    (hTransport : transport' = transport) (hReplay : replay' = replay)
    (hProvenance : provenance' = provenance) (hName : localName' = localName) :
    FiniteRelationUp.mk leftSurface' rightSurface' relationRows' membership' domainSupport'
        rangeSupport' transport' replay' provenance' localName' =
      FiniteRelationUp.mk leftSurface rightSurface relationRows membership domainSupport
        rangeSupport transport replay provenance localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hLeft
  cases hRight
  cases hRows
  cases hMember
  cases hDomain
  cases hRange
  cases hTransport
  cases hReplay
  cases hProvenance
  cases hName
  rfl

private theorem FiniteRelationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FiniteRelationUp,
      finiteRelationFromEventFlow (finiteRelationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk leftSurface rightSurface relationRows membership domainSupport rangeSupport transport
      replay provenance localName =>
      exact
        congrArg some
          (finiteRelation_mk_congr
            (FiniteRelationTasteGate_single_carrier_alignment_decode leftSurface)
            (FiniteRelationTasteGate_single_carrier_alignment_decode rightSurface)
            (FiniteRelationTasteGate_single_carrier_alignment_decode relationRows)
            (FiniteRelationTasteGate_single_carrier_alignment_decode membership)
            (FiniteRelationTasteGate_single_carrier_alignment_decode domainSupport)
            (FiniteRelationTasteGate_single_carrier_alignment_decode rangeSupport)
            (FiniteRelationTasteGate_single_carrier_alignment_decode transport)
            (FiniteRelationTasteGate_single_carrier_alignment_decode replay)
            (FiniteRelationTasteGate_single_carrier_alignment_decode provenance)
            (FiniteRelationTasteGate_single_carrier_alignment_decode localName))

private theorem finiteRelationToEventFlow_injective {x y : FiniteRelationUp} :
    finiteRelationToEventFlow x = finiteRelationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteRelationFromEventFlow (finiteRelationToEventFlow x) =
        finiteRelationFromEventFlow (finiteRelationToEventFlow y) :=
    congrArg finiteRelationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FiniteRelationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FiniteRelationTasteGate_single_carrier_alignment_round_trip y)))

private theorem finiteRelation_field_faithful :
    ∀ x y : FiniteRelationUp, finiteRelationFields x = finiteRelationFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk leftSurface rightSurface relationRows membership domainSupport rangeSupport transport
      replay provenance localName =>
      cases y with
      | mk leftSurface' rightSurface' relationRows' membership' domainSupport' rangeSupport'
          transport' replay' provenance' localName' =>
          cases hfields
          rfl

instance finiteRelationBHistCarrier : BHistCarrier FiniteRelationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteRelationToEventFlow
  fromEventFlow := finiteRelationFromEventFlow

instance finiteRelationChapterTasteGate : ChapterTasteGate FiniteRelationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteRelationFromEventFlow (finiteRelationToEventFlow x) = some x
    exact FiniteRelationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteRelationToEventFlow_injective heq)

instance finiteRelationFieldFaithful : FieldFaithful FiniteRelationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteRelationFields
  field_faithful := finiteRelation_field_faithful

instance finiteRelationNontrivial : BEDC.Meta.TasteGate.Nontrivial FiniteRelationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteRelationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteRelationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteRelationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteRelationChapterTasteGate

theorem FiniteRelationTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate FiniteRelationUp) ∧
      Nonempty (FieldFaithful FiniteRelationUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial FiniteRelationUp) ∧
      (∀ h : BHist, finiteRelationDecodeBHist (finiteRelationEncodeBHist h) = h) ∧
      (∀ x : FiniteRelationUp,
        finiteRelationFromEventFlow (finiteRelationToEventFlow x) = some x) ∧
      (∀ x y : FiniteRelationUp,
        finiteRelationToEventFlow x = finiteRelationToEventFlow y → x = y) ∧
      finiteRelationEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨finiteRelationChapterTasteGate⟩
  constructor
  · exact ⟨finiteRelationFieldFaithful⟩
  constructor
  · exact ⟨finiteRelationNontrivial⟩
  constructor
  · exact FiniteRelationTasteGate_single_carrier_alignment_decode
  constructor
  · exact FiniteRelationTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact finiteRelationToEventFlow_injective heq
  · rfl

end BEDC.Derived.FiniteRelationUp
