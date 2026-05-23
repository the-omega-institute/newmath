import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ProductFilterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ProductFilterUp : Type where
  | mk
      (componentBaseX componentBaseY productIndex projectionX projectionY lowerBound
        refinement transport replay provenance localName : BHist) :
      ProductFilterUp
  deriving DecidableEq

def productFilterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: productFilterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: productFilterEncodeBHist h

def productFilterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (productFilterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (productFilterDecodeBHist tail)

private theorem ProductFilterTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, productFilterDecodeBHist (productFilterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def productFilterFields : ProductFilterUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ProductFilterUp.mk componentBaseX componentBaseY productIndex projectionX projectionY
      lowerBound refinement transport replay provenance localName =>
      [componentBaseX, componentBaseY, productIndex, projectionX, projectionY, lowerBound,
        refinement, transport, replay, provenance, localName]

def productFilterToEventFlow : ProductFilterUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (productFilterFields x).map productFilterEncodeBHist

private def productFilterEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => productFilterEventAtDefault index rest

def productFilterFromEventFlow (ef : EventFlow) : Option ProductFilterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ProductFilterUp.mk
      (productFilterDecodeBHist (productFilterEventAtDefault 0 ef))
      (productFilterDecodeBHist (productFilterEventAtDefault 1 ef))
      (productFilterDecodeBHist (productFilterEventAtDefault 2 ef))
      (productFilterDecodeBHist (productFilterEventAtDefault 3 ef))
      (productFilterDecodeBHist (productFilterEventAtDefault 4 ef))
      (productFilterDecodeBHist (productFilterEventAtDefault 5 ef))
      (productFilterDecodeBHist (productFilterEventAtDefault 6 ef))
      (productFilterDecodeBHist (productFilterEventAtDefault 7 ef))
      (productFilterDecodeBHist (productFilterEventAtDefault 8 ef))
      (productFilterDecodeBHist (productFilterEventAtDefault 9 ef))
      (productFilterDecodeBHist (productFilterEventAtDefault 10 ef)))

private theorem ProductFilterTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ProductFilterUp,
      productFilterFromEventFlow (productFilterToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk componentBaseX componentBaseY productIndex projectionX projectionY lowerBound
      refinement transport replay provenance localName =>
      change
        some
          (ProductFilterUp.mk
            (productFilterDecodeBHist (productFilterEncodeBHist componentBaseX))
            (productFilterDecodeBHist (productFilterEncodeBHist componentBaseY))
            (productFilterDecodeBHist (productFilterEncodeBHist productIndex))
            (productFilterDecodeBHist (productFilterEncodeBHist projectionX))
            (productFilterDecodeBHist (productFilterEncodeBHist projectionY))
            (productFilterDecodeBHist (productFilterEncodeBHist lowerBound))
            (productFilterDecodeBHist (productFilterEncodeBHist refinement))
            (productFilterDecodeBHist (productFilterEncodeBHist transport))
            (productFilterDecodeBHist (productFilterEncodeBHist replay))
            (productFilterDecodeBHist (productFilterEncodeBHist provenance))
            (productFilterDecodeBHist (productFilterEncodeBHist localName))) =
          some
            (ProductFilterUp.mk componentBaseX componentBaseY productIndex projectionX
              projectionY lowerBound refinement transport replay provenance localName)
      rw [ProductFilterTasteGate_single_carrier_alignment_decode componentBaseX,
        ProductFilterTasteGate_single_carrier_alignment_decode componentBaseY,
        ProductFilterTasteGate_single_carrier_alignment_decode productIndex,
        ProductFilterTasteGate_single_carrier_alignment_decode projectionX,
        ProductFilterTasteGate_single_carrier_alignment_decode projectionY,
        ProductFilterTasteGate_single_carrier_alignment_decode lowerBound,
        ProductFilterTasteGate_single_carrier_alignment_decode refinement,
        ProductFilterTasteGate_single_carrier_alignment_decode transport,
        ProductFilterTasteGate_single_carrier_alignment_decode replay,
        ProductFilterTasteGate_single_carrier_alignment_decode provenance,
        ProductFilterTasteGate_single_carrier_alignment_decode localName]

private theorem ProductFilterTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ProductFilterUp} :
    productFilterToEventFlow x = productFilterToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      productFilterFromEventFlow (productFilterToEventFlow x) =
        productFilterFromEventFlow (productFilterToEventFlow y) :=
    congrArg productFilterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ProductFilterTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ProductFilterTasteGate_single_carrier_alignment_round_trip y)))

private theorem ProductFilterTasteGate_single_carrier_alignment_fields :
    ∀ x y : ProductFilterUp, productFilterFields x = productFilterFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk componentBaseX1 componentBaseY1 productIndex1 projectionX1 projectionY1 lowerBound1
      refinement1 transport1 replay1 provenance1 localName1 =>
      cases y with
      | mk componentBaseX2 componentBaseY2 productIndex2 projectionX2 projectionY2 lowerBound2
          refinement2 transport2 replay2 provenance2 localName2 =>
          cases hfields
          rfl

instance productFilterBHistCarrier : BHistCarrier ProductFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := productFilterToEventFlow
  fromEventFlow := productFilterFromEventFlow

instance productFilterChapterTasteGate : ChapterTasteGate ProductFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change productFilterFromEventFlow (productFilterToEventFlow x) = some x
    exact ProductFilterTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ProductFilterTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance productFilterFieldFaithful : FieldFaithful ProductFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := productFilterFields
  field_faithful := ProductFilterTasteGate_single_carrier_alignment_fields

instance productFilterNontrivial : Nontrivial ProductFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ProductFilterUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ProductFilterUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ProductFilterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  productFilterChapterTasteGate

theorem ProductFilterTasteGate_single_carrier_alignment :
    (∀ h : BHist, productFilterDecodeBHist (productFilterEncodeBHist h) = h) ∧
      (∀ x : ProductFilterUp, productFilterFromEventFlow (productFilterToEventFlow x) = some x) ∧
        (∀ x y : ProductFilterUp,
          productFilterToEventFlow x = productFilterToEventFlow y → x = y) ∧
          productFilterEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨ProductFilterTasteGate_single_carrier_alignment_decode,
      ProductFilterTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => ProductFilterTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ProductFilterUp
