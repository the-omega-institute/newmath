import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EnrichedYonedaUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EnrichedYonedaUp : Type where
  | mk
      (category enrichedCategory object homObject functorPoint naturality monoidalCoherence
        transport route readback provenance name : BHist) :
      EnrichedYonedaUp
  deriving DecidableEq

def enrichedYonedaEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: enrichedYonedaEncodeBHist h
  | BHist.e1 h => BMark.b1 :: enrichedYonedaEncodeBHist h

def enrichedYonedaDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (enrichedYonedaDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (enrichedYonedaDecodeBHist tail)

private theorem enrichedYoneda_decode_encode_bhist :
    ∀ h : BHist, enrichedYonedaDecodeBHist (enrichedYonedaEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem enrichedYoneda_mk_congr
    {category category' enrichedCategory enrichedCategory' object object' homObject homObject'
      functorPoint functorPoint' naturality naturality' monoidalCoherence
      monoidalCoherence' transport transport' route route' readback readback'
      provenance provenance' name name' : BHist}
    (hcategory : category' = category) (henrichedCategory : enrichedCategory' = enrichedCategory)
    (hobject : object' = object) (hhomObject : homObject' = homObject)
    (hfunctorPoint : functorPoint' = functorPoint) (hnaturality : naturality' = naturality)
    (hmonoidalCoherence : monoidalCoherence' = monoidalCoherence)
    (htransport : transport' = transport) (hroute : route' = route)
    (hreadback : readback' = readback) (hprovenance : provenance' = provenance)
    (hname : name' = name) :
    EnrichedYonedaUp.mk category' enrichedCategory' object' homObject' functorPoint'
        naturality' monoidalCoherence' transport' route' readback' provenance' name' =
      EnrichedYonedaUp.mk category enrichedCategory object homObject functorPoint naturality
        monoidalCoherence transport route readback provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hcategory
  cases henrichedCategory
  cases hobject
  cases hhomObject
  cases hfunctorPoint
  cases hnaturality
  cases hmonoidalCoherence
  cases htransport
  cases hroute
  cases hreadback
  cases hprovenance
  cases hname
  rfl

def enrichedYonedaFields : EnrichedYonedaUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EnrichedYonedaUp.mk category enrichedCategory object homObject functorPoint naturality
      monoidalCoherence transport route readback provenance name =>
      [category, enrichedCategory, object, homObject, functorPoint, naturality,
        monoidalCoherence, transport, route, readback, provenance, name]

def enrichedYonedaToEventFlow : EnrichedYonedaUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (enrichedYonedaFields x).map enrichedYonedaEncodeBHist

def enrichedYonedaFromEventFlow : EventFlow → Option EnrichedYonedaUp
  -- BEDC touchpoint anchor: BHist BMark
  | category :: enrichedCategory :: object :: homObject :: functorPoint :: naturality ::
      monoidalCoherence :: transport :: route :: readback :: provenance :: name :: [] =>
      some
        (EnrichedYonedaUp.mk
          (enrichedYonedaDecodeBHist category)
          (enrichedYonedaDecodeBHist enrichedCategory)
          (enrichedYonedaDecodeBHist object)
          (enrichedYonedaDecodeBHist homObject)
          (enrichedYonedaDecodeBHist functorPoint)
          (enrichedYonedaDecodeBHist naturality)
          (enrichedYonedaDecodeBHist monoidalCoherence)
          (enrichedYonedaDecodeBHist transport)
          (enrichedYonedaDecodeBHist route)
          (enrichedYonedaDecodeBHist readback)
          (enrichedYonedaDecodeBHist provenance)
          (enrichedYonedaDecodeBHist name))
  | _ => none

private theorem enrichedYoneda_round_trip :
    ∀ x : EnrichedYonedaUp,
      enrichedYonedaFromEventFlow (enrichedYonedaToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk category enrichedCategory object homObject functorPoint naturality monoidalCoherence
      transport route readback provenance name =>
      exact
        congrArg some
          (enrichedYoneda_mk_congr
            (enrichedYoneda_decode_encode_bhist category)
            (enrichedYoneda_decode_encode_bhist enrichedCategory)
            (enrichedYoneda_decode_encode_bhist object)
            (enrichedYoneda_decode_encode_bhist homObject)
            (enrichedYoneda_decode_encode_bhist functorPoint)
            (enrichedYoneda_decode_encode_bhist naturality)
            (enrichedYoneda_decode_encode_bhist monoidalCoherence)
            (enrichedYoneda_decode_encode_bhist transport)
            (enrichedYoneda_decode_encode_bhist route)
            (enrichedYoneda_decode_encode_bhist readback)
            (enrichedYoneda_decode_encode_bhist provenance)
            (enrichedYoneda_decode_encode_bhist name))

private theorem enrichedYonedaToEventFlow_injective {x y : EnrichedYonedaUp} :
    enrichedYonedaToEventFlow x = enrichedYonedaToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      enrichedYonedaFromEventFlow (enrichedYonedaToEventFlow x) =
        enrichedYonedaFromEventFlow (enrichedYonedaToEventFlow y) :=
    congrArg enrichedYonedaFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (enrichedYoneda_round_trip x).symm
      (Eq.trans hread (enrichedYoneda_round_trip y)))

private theorem enrichedYoneda_field_faithful :
    ∀ x y : EnrichedYonedaUp, enrichedYonedaFields x = enrichedYonedaFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk category enrichedCategory object homObject functorPoint naturality monoidalCoherence
      transport route readback provenance name =>
      cases y with
      | mk category' enrichedCategory' object' homObject' functorPoint' naturality'
          monoidalCoherence' transport' route' readback' provenance' name' =>
          cases hfields
          rfl

instance enrichedYonedaBHistCarrier : BHistCarrier EnrichedYonedaUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := enrichedYonedaToEventFlow
  fromEventFlow := enrichedYonedaFromEventFlow

instance enrichedYonedaChapterTasteGate : ChapterTasteGate EnrichedYonedaUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change enrichedYonedaFromEventFlow (enrichedYonedaToEventFlow x) = some x
    exact enrichedYoneda_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (enrichedYonedaToEventFlow_injective heq)

instance enrichedYonedaFieldFaithful : FieldFaithful EnrichedYonedaUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := enrichedYonedaFields
  field_faithful := enrichedYoneda_field_faithful

instance enrichedYonedaNontrivial : BEDC.Meta.TasteGate.Nontrivial EnrichedYonedaUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨EnrichedYonedaUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      EnrichedYonedaUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate EnrichedYonedaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  enrichedYonedaChapterTasteGate

end BEDC.Derived.EnrichedYonedaUp
