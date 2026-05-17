import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SubjectIndexRouteUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SubjectIndexRouteUp : Type where
  | mk :
      (ordinary coreRegistry conceptRegistry registryExport consistencyGate traditionBridge
        transport replay provenance name : BHist) →
      SubjectIndexRouteUp
  deriving DecidableEq

def subjectIndexRouteEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: subjectIndexRouteEncodeBHist h
  | BHist.e1 h => BMark.b1 :: subjectIndexRouteEncodeBHist h

def subjectIndexRouteDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (subjectIndexRouteDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (subjectIndexRouteDecodeBHist tail)

private theorem subjectIndexRoute_decode_encode_bhist :
    ∀ h : BHist, subjectIndexRouteDecodeBHist (subjectIndexRouteEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem subjectIndexRoute_mk_congr
    {ordinary ordinary' coreRegistry coreRegistry' conceptRegistry conceptRegistry'
      registryExport registryExport' consistencyGate consistencyGate'
      traditionBridge traditionBridge' transport transport' replay replay'
      provenance provenance' name name' : BHist}
    (hOrdinary : ordinary' = ordinary)
    (hCoreRegistry : coreRegistry' = coreRegistry)
    (hConceptRegistry : conceptRegistry' = conceptRegistry)
    (hRegistryExport : registryExport' = registryExport)
    (hConsistencyGate : consistencyGate' = consistencyGate)
    (hTraditionBridge : traditionBridge' = traditionBridge)
    (hTransport : transport' = transport)
    (hReplay : replay' = replay)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    SubjectIndexRouteUp.mk ordinary' coreRegistry' conceptRegistry' registryExport'
        consistencyGate' traditionBridge' transport' replay' provenance' name' =
      SubjectIndexRouteUp.mk ordinary coreRegistry conceptRegistry registryExport
        consistencyGate traditionBridge transport replay provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hOrdinary
  cases hCoreRegistry
  cases hConceptRegistry
  cases hRegistryExport
  cases hConsistencyGate
  cases hTraditionBridge
  cases hTransport
  cases hReplay
  cases hProvenance
  cases hName
  rfl

def subjectIndexRouteFields :
    SubjectIndexRouteUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SubjectIndexRouteUp.mk ordinary coreRegistry conceptRegistry registryExport consistencyGate
      traditionBridge transport replay provenance name =>
      [ordinary, coreRegistry, conceptRegistry, registryExport, consistencyGate, traditionBridge,
        transport, replay, provenance, name]

def subjectIndexRouteToEventFlow :
    SubjectIndexRouteUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SubjectIndexRouteUp.mk ordinary coreRegistry conceptRegistry registryExport consistencyGate
      traditionBridge transport replay provenance name =>
      [subjectIndexRouteEncodeBHist ordinary,
        subjectIndexRouteEncodeBHist coreRegistry,
        subjectIndexRouteEncodeBHist conceptRegistry,
        subjectIndexRouteEncodeBHist registryExport,
        subjectIndexRouteEncodeBHist consistencyGate,
        subjectIndexRouteEncodeBHist traditionBridge,
        subjectIndexRouteEncodeBHist transport,
        subjectIndexRouteEncodeBHist replay,
        subjectIndexRouteEncodeBHist provenance,
        subjectIndexRouteEncodeBHist name]

private def subjectIndexRouteEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      subjectIndexRouteEventAtDefault index rest

def subjectIndexRouteFromEventFlow : EventFlow → Option SubjectIndexRouteUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (SubjectIndexRouteUp.mk
        (subjectIndexRouteDecodeBHist (subjectIndexRouteEventAtDefault 0 ef))
        (subjectIndexRouteDecodeBHist (subjectIndexRouteEventAtDefault 1 ef))
        (subjectIndexRouteDecodeBHist (subjectIndexRouteEventAtDefault 2 ef))
        (subjectIndexRouteDecodeBHist (subjectIndexRouteEventAtDefault 3 ef))
        (subjectIndexRouteDecodeBHist (subjectIndexRouteEventAtDefault 4 ef))
        (subjectIndexRouteDecodeBHist (subjectIndexRouteEventAtDefault 5 ef))
        (subjectIndexRouteDecodeBHist (subjectIndexRouteEventAtDefault 6 ef))
        (subjectIndexRouteDecodeBHist (subjectIndexRouteEventAtDefault 7 ef))
        (subjectIndexRouteDecodeBHist (subjectIndexRouteEventAtDefault 8 ef))
        (subjectIndexRouteDecodeBHist (subjectIndexRouteEventAtDefault 9 ef)))

private theorem subjectIndexRoute_round_trip :
    ∀ x : SubjectIndexRouteUp,
      subjectIndexRouteFromEventFlow (subjectIndexRouteToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk ordinary coreRegistry conceptRegistry registryExport consistencyGate traditionBridge
      transport replay provenance name =>
      exact
        congrArg some
          (subjectIndexRoute_mk_congr
            (subjectIndexRoute_decode_encode_bhist ordinary)
            (subjectIndexRoute_decode_encode_bhist coreRegistry)
            (subjectIndexRoute_decode_encode_bhist conceptRegistry)
            (subjectIndexRoute_decode_encode_bhist registryExport)
            (subjectIndexRoute_decode_encode_bhist consistencyGate)
            (subjectIndexRoute_decode_encode_bhist traditionBridge)
            (subjectIndexRoute_decode_encode_bhist transport)
            (subjectIndexRoute_decode_encode_bhist replay)
            (subjectIndexRoute_decode_encode_bhist provenance)
            (subjectIndexRoute_decode_encode_bhist name))

private theorem subjectIndexRouteToEventFlow_injective {x y : SubjectIndexRouteUp} :
    subjectIndexRouteToEventFlow x = subjectIndexRouteToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      subjectIndexRouteFromEventFlow (subjectIndexRouteToEventFlow x) =
        subjectIndexRouteFromEventFlow (subjectIndexRouteToEventFlow y) :=
    congrArg subjectIndexRouteFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (subjectIndexRoute_round_trip x).symm
      (Eq.trans hread (subjectIndexRoute_round_trip y)))

private theorem subjectIndexRoute_field_faithful :
    ∀ x y : SubjectIndexRouteUp,
      subjectIndexRouteFields x = subjectIndexRouteFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk ordinary coreRegistry conceptRegistry registryExport consistencyGate traditionBridge
      transport replay provenance name =>
      cases y with
      | mk ordinary' coreRegistry' conceptRegistry' registryExport' consistencyGate'
          traditionBridge' transport' replay' provenance' name' =>
          cases hfields
          rfl

instance subjectIndexRouteBHistCarrier : BHistCarrier SubjectIndexRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := subjectIndexRouteToEventFlow
  fromEventFlow := subjectIndexRouteFromEventFlow

instance subjectIndexRouteChapterTasteGate :
    ChapterTasteGate SubjectIndexRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change subjectIndexRouteFromEventFlow (subjectIndexRouteToEventFlow x) = some x
    exact subjectIndexRoute_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (subjectIndexRouteToEventFlow_injective heq)

instance subjectIndexRouteFieldFaithful :
    FieldFaithful SubjectIndexRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := subjectIndexRouteFields
  field_faithful := subjectIndexRoute_field_faithful

instance subjectIndexRouteNontrivial : Nontrivial SubjectIndexRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SubjectIndexRouteUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SubjectIndexRouteUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SubjectIndexRouteUp :=
  -- BEDC touchpoint anchor: BHist BMark
  subjectIndexRouteChapterTasteGate

theorem SubjectIndexRouteUp_single_carrier_alignment :
    Nonempty (ChapterTasteGate SubjectIndexRouteUp) ∧
      Nonempty (FieldFaithful SubjectIndexRouteUp) ∧
        Nonempty (Nontrivial SubjectIndexRouteUp) ∧
          (∃ x : SubjectIndexRouteUp,
            FieldFaithful.fields x =
              [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
                BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty]) ∧
            SubjectIndexRouteUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty ≠
              SubjectIndexRouteUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty := by
  -- BEDC touchpoint anchor: BHist BMark
  refine ⟨⟨subjectIndexRouteChapterTasteGate⟩,
    ⟨subjectIndexRouteFieldFaithful⟩,
    ⟨subjectIndexRouteNontrivial⟩, ?_, ?_⟩
  · exact
      ⟨SubjectIndexRouteUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty, rfl⟩
  · intro h
    cases h

end BEDC.Derived.SubjectIndexRouteUp
