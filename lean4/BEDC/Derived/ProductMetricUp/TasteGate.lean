import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ProductMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ProductMetricUp : Type where
  | mk (X Y dX dY Pi delta H C P N : BHist) : ProductMetricUp
  deriving DecidableEq

def productMetricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: productMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: productMetricEncodeBHist h

def productMetricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (productMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (productMetricDecodeBHist tail)

private theorem ProductMetricTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, productMetricDecodeBHist (productMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def productMetricFields : ProductMetricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ProductMetricUp.mk X Y dX dY Pi delta H C P N =>
      [X, Y, dX, dY, Pi, delta, H, C, P, N]

def productMetricToEventFlow : ProductMetricUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (productMetricFields x).map productMetricEncodeBHist

private def productMetricEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => productMetricEventAtDefault index rest

def productMetricFromEventFlow (ef : EventFlow) : Option ProductMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ProductMetricUp.mk
      (productMetricDecodeBHist (productMetricEventAtDefault 0 ef))
      (productMetricDecodeBHist (productMetricEventAtDefault 1 ef))
      (productMetricDecodeBHist (productMetricEventAtDefault 2 ef))
      (productMetricDecodeBHist (productMetricEventAtDefault 3 ef))
      (productMetricDecodeBHist (productMetricEventAtDefault 4 ef))
      (productMetricDecodeBHist (productMetricEventAtDefault 5 ef))
      (productMetricDecodeBHist (productMetricEventAtDefault 6 ef))
      (productMetricDecodeBHist (productMetricEventAtDefault 7 ef))
      (productMetricDecodeBHist (productMetricEventAtDefault 8 ef))
      (productMetricDecodeBHist (productMetricEventAtDefault 9 ef)))

private theorem ProductMetricTasteGate_single_carrier_alignment_round_trip
    (x : ProductMetricUp) :
    productMetricFromEventFlow (productMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X Y dX dY Pi delta H C P N =>
      change
        some
          (ProductMetricUp.mk
            (productMetricDecodeBHist (productMetricEncodeBHist X))
            (productMetricDecodeBHist (productMetricEncodeBHist Y))
            (productMetricDecodeBHist (productMetricEncodeBHist dX))
            (productMetricDecodeBHist (productMetricEncodeBHist dY))
            (productMetricDecodeBHist (productMetricEncodeBHist Pi))
            (productMetricDecodeBHist (productMetricEncodeBHist delta))
            (productMetricDecodeBHist (productMetricEncodeBHist H))
            (productMetricDecodeBHist (productMetricEncodeBHist C))
            (productMetricDecodeBHist (productMetricEncodeBHist P))
            (productMetricDecodeBHist (productMetricEncodeBHist N))) =
          some (ProductMetricUp.mk X Y dX dY Pi delta H C P N)
      rw [ProductMetricTasteGate_single_carrier_alignment_decode X,
        ProductMetricTasteGate_single_carrier_alignment_decode Y,
        ProductMetricTasteGate_single_carrier_alignment_decode dX,
        ProductMetricTasteGate_single_carrier_alignment_decode dY,
        ProductMetricTasteGate_single_carrier_alignment_decode Pi,
        ProductMetricTasteGate_single_carrier_alignment_decode delta,
        ProductMetricTasteGate_single_carrier_alignment_decode H,
        ProductMetricTasteGate_single_carrier_alignment_decode C,
        ProductMetricTasteGate_single_carrier_alignment_decode P,
        ProductMetricTasteGate_single_carrier_alignment_decode N]

private theorem ProductMetricTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ProductMetricUp} :
    productMetricToEventFlow x = productMetricToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      productMetricFromEventFlow (productMetricToEventFlow x) =
        productMetricFromEventFlow (productMetricToEventFlow y) :=
    congrArg productMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ProductMetricTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ProductMetricTasteGate_single_carrier_alignment_round_trip y)))

private theorem ProductMetricTasteGate_single_carrier_alignment_fields :
    ∀ x y : ProductMetricUp, productMetricFields x = productMetricFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 Y1 dX1 dY1 Pi1 delta1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 Y2 dX2 dY2 Pi2 delta2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance productMetricBHistCarrier : BHistCarrier ProductMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := productMetricToEventFlow
  fromEventFlow := productMetricFromEventFlow

instance productMetricChapterTasteGate : ChapterTasteGate ProductMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change productMetricFromEventFlow (productMetricToEventFlow x) = some x
    exact ProductMetricTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ProductMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance productMetricFieldFaithful : FieldFaithful ProductMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := productMetricFields
  field_faithful := ProductMetricTasteGate_single_carrier_alignment_fields

instance productMetricNontrivial : Nontrivial ProductMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ProductMetricUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ProductMetricUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def productMetricTasteGate : ChapterTasteGate ProductMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  productMetricChapterTasteGate

theorem ProductMetricTasteGate_single_carrier_alignment :
    (∀ h : BHist, productMetricDecodeBHist (productMetricEncodeBHist h) = h) ∧
      (∀ x : ProductMetricUp,
        productMetricFromEventFlow (productMetricToEventFlow x) = some x) ∧
        (∀ x y : ProductMetricUp,
          productMetricToEventFlow x = productMetricToEventFlow y → x = y) ∧
          productMetricEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨ProductMetricTasteGate_single_carrier_alignment_decode,
      ProductMetricTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => ProductMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ProductMetricUp
