import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ProductTopologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ProductTopologyUp : Type where
  | mk (X Y OX OY Pi piX piY B T H C P N : BHist) : ProductTopologyUp
  deriving DecidableEq

def productTopologyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: productTopologyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: productTopologyEncodeBHist h

def productTopologyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (productTopologyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (productTopologyDecodeBHist tail)

private theorem ProductTopologyTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, productTopologyDecodeBHist (productTopologyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def productTopologyFields : ProductTopologyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ProductTopologyUp.mk X Y OX OY Pi piX piY B T H C P N =>
      [X, Y, OX, OY, Pi, piX, piY, B, T, H, C, P, N]

def productTopologyToEventFlow : ProductTopologyUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (productTopologyFields x).map productTopologyEncodeBHist

private def productTopologyEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => productTopologyEventAtDefault index rest

def productTopologyFromEventFlow (ef : EventFlow) : Option ProductTopologyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ProductTopologyUp.mk
      (productTopologyDecodeBHist (productTopologyEventAtDefault 0 ef))
      (productTopologyDecodeBHist (productTopologyEventAtDefault 1 ef))
      (productTopologyDecodeBHist (productTopologyEventAtDefault 2 ef))
      (productTopologyDecodeBHist (productTopologyEventAtDefault 3 ef))
      (productTopologyDecodeBHist (productTopologyEventAtDefault 4 ef))
      (productTopologyDecodeBHist (productTopologyEventAtDefault 5 ef))
      (productTopologyDecodeBHist (productTopologyEventAtDefault 6 ef))
      (productTopologyDecodeBHist (productTopologyEventAtDefault 7 ef))
      (productTopologyDecodeBHist (productTopologyEventAtDefault 8 ef))
      (productTopologyDecodeBHist (productTopologyEventAtDefault 9 ef))
      (productTopologyDecodeBHist (productTopologyEventAtDefault 10 ef))
      (productTopologyDecodeBHist (productTopologyEventAtDefault 11 ef))
      (productTopologyDecodeBHist (productTopologyEventAtDefault 12 ef)))

private theorem ProductTopologyTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ProductTopologyUp,
      productTopologyFromEventFlow (productTopologyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk X Y OX OY Pi piX piY B T H C P N =>
      change
        some
          (ProductTopologyUp.mk
            (productTopologyDecodeBHist (productTopologyEncodeBHist X))
            (productTopologyDecodeBHist (productTopologyEncodeBHist Y))
            (productTopologyDecodeBHist (productTopologyEncodeBHist OX))
            (productTopologyDecodeBHist (productTopologyEncodeBHist OY))
            (productTopologyDecodeBHist (productTopologyEncodeBHist Pi))
            (productTopologyDecodeBHist (productTopologyEncodeBHist piX))
            (productTopologyDecodeBHist (productTopologyEncodeBHist piY))
            (productTopologyDecodeBHist (productTopologyEncodeBHist B))
            (productTopologyDecodeBHist (productTopologyEncodeBHist T))
            (productTopologyDecodeBHist (productTopologyEncodeBHist H))
            (productTopologyDecodeBHist (productTopologyEncodeBHist C))
            (productTopologyDecodeBHist (productTopologyEncodeBHist P))
            (productTopologyDecodeBHist (productTopologyEncodeBHist N))) =
          some (ProductTopologyUp.mk X Y OX OY Pi piX piY B T H C P N)
      rw [ProductTopologyTasteGate_single_carrier_alignment_decode X,
        ProductTopologyTasteGate_single_carrier_alignment_decode Y,
        ProductTopologyTasteGate_single_carrier_alignment_decode OX,
        ProductTopologyTasteGate_single_carrier_alignment_decode OY,
        ProductTopologyTasteGate_single_carrier_alignment_decode Pi,
        ProductTopologyTasteGate_single_carrier_alignment_decode piX,
        ProductTopologyTasteGate_single_carrier_alignment_decode piY,
        ProductTopologyTasteGate_single_carrier_alignment_decode B,
        ProductTopologyTasteGate_single_carrier_alignment_decode T,
        ProductTopologyTasteGate_single_carrier_alignment_decode H,
        ProductTopologyTasteGate_single_carrier_alignment_decode C,
        ProductTopologyTasteGate_single_carrier_alignment_decode P,
        ProductTopologyTasteGate_single_carrier_alignment_decode N]

private theorem ProductTopologyTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ProductTopologyUp} :
    productTopologyToEventFlow x = productTopologyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      productTopologyFromEventFlow (productTopologyToEventFlow x) =
        productTopologyFromEventFlow (productTopologyToEventFlow y) :=
    congrArg productTopologyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ProductTopologyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (ProductTopologyTasteGate_single_carrier_alignment_round_trip y)))

private theorem ProductTopologyTasteGate_single_carrier_alignment_fields :
    ∀ x y : ProductTopologyUp, productTopologyFields x = productTopologyFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 Y1 OX1 OY1 Pi1 piX1 piY1 B1 T1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 Y2 OX2 OY2 Pi2 piX2 piY2 B2 T2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance productTopologyBHistCarrier : BHistCarrier ProductTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := productTopologyToEventFlow
  fromEventFlow := productTopologyFromEventFlow

instance productTopologyChapterTasteGate : ChapterTasteGate ProductTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change productTopologyFromEventFlow (productTopologyToEventFlow x) = some x
    exact ProductTopologyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ProductTopologyTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance productTopologyFieldFaithful : FieldFaithful ProductTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := productTopologyFields
  field_faithful := ProductTopologyTasteGate_single_carrier_alignment_fields

instance productTopologyNontrivial : Nontrivial ProductTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ProductTopologyUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      ProductTopologyUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ProductTopologyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  productTopologyChapterTasteGate

theorem ProductTopologyTasteGate_single_carrier_alignment :
    (∀ h : BHist, productTopologyDecodeBHist (productTopologyEncodeBHist h) = h) ∧
      (∀ x : ProductTopologyUp,
        productTopologyFromEventFlow (productTopologyToEventFlow x) = some x) ∧
        (∀ x y : ProductTopologyUp,
          productTopologyToEventFlow x = productTopologyToEventFlow y → x = y) ∧
          productTopologyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨ProductTopologyTasteGate_single_carrier_alignment_decode,
      ProductTopologyTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        ProductTopologyTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ProductTopologyUp
