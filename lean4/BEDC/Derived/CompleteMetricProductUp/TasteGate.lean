import BEDC.Derived.CompleteMetricProductUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompleteMetricProductUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def completeMetricProductEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: completeMetricProductEncodeBHist h
  | BHist.e1 h => BMark.b1 :: completeMetricProductEncodeBHist h

def completeMetricProductDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (completeMetricProductDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (completeMetricProductDecodeBHist tail)

private theorem CompleteMetricProductTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, completeMetricProductDecodeBHist
      (completeMetricProductEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def completeMetricProductFields : CompleteMetricProductUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompleteMetricProductUp.mk M X Y SX SY RX RY AX AY LX LY Pi L H C P N =>
      [M, X, Y, SX, SY, RX, RY, AX, AY, LX, LY, Pi, L, H, C, P, N]

def completeMetricProductToEventFlow : CompleteMetricProductUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (completeMetricProductFields x).map completeMetricProductEncodeBHist

private def completeMetricProductEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => completeMetricProductEventAtDefault index rest

def completeMetricProductFromEventFlow (ef : EventFlow) : Option CompleteMetricProductUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompleteMetricProductUp.mk
      (completeMetricProductDecodeBHist (completeMetricProductEventAtDefault 0 ef))
      (completeMetricProductDecodeBHist (completeMetricProductEventAtDefault 1 ef))
      (completeMetricProductDecodeBHist (completeMetricProductEventAtDefault 2 ef))
      (completeMetricProductDecodeBHist (completeMetricProductEventAtDefault 3 ef))
      (completeMetricProductDecodeBHist (completeMetricProductEventAtDefault 4 ef))
      (completeMetricProductDecodeBHist (completeMetricProductEventAtDefault 5 ef))
      (completeMetricProductDecodeBHist (completeMetricProductEventAtDefault 6 ef))
      (completeMetricProductDecodeBHist (completeMetricProductEventAtDefault 7 ef))
      (completeMetricProductDecodeBHist (completeMetricProductEventAtDefault 8 ef))
      (completeMetricProductDecodeBHist (completeMetricProductEventAtDefault 9 ef))
      (completeMetricProductDecodeBHist (completeMetricProductEventAtDefault 10 ef))
      (completeMetricProductDecodeBHist (completeMetricProductEventAtDefault 11 ef))
      (completeMetricProductDecodeBHist (completeMetricProductEventAtDefault 12 ef))
      (completeMetricProductDecodeBHist (completeMetricProductEventAtDefault 13 ef))
      (completeMetricProductDecodeBHist (completeMetricProductEventAtDefault 14 ef))
      (completeMetricProductDecodeBHist (completeMetricProductEventAtDefault 15 ef))
      (completeMetricProductDecodeBHist (completeMetricProductEventAtDefault 16 ef)))

private theorem CompleteMetricProductTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompleteMetricProductUp,
      completeMetricProductFromEventFlow
        (completeMetricProductToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk M X Y SX SY RX RY AX AY LX LY Pi L H C P N =>
      change
        some
          (CompleteMetricProductUp.mk
            (completeMetricProductDecodeBHist (completeMetricProductEncodeBHist M))
            (completeMetricProductDecodeBHist (completeMetricProductEncodeBHist X))
            (completeMetricProductDecodeBHist (completeMetricProductEncodeBHist Y))
            (completeMetricProductDecodeBHist (completeMetricProductEncodeBHist SX))
            (completeMetricProductDecodeBHist (completeMetricProductEncodeBHist SY))
            (completeMetricProductDecodeBHist (completeMetricProductEncodeBHist RX))
            (completeMetricProductDecodeBHist (completeMetricProductEncodeBHist RY))
            (completeMetricProductDecodeBHist (completeMetricProductEncodeBHist AX))
            (completeMetricProductDecodeBHist (completeMetricProductEncodeBHist AY))
            (completeMetricProductDecodeBHist (completeMetricProductEncodeBHist LX))
            (completeMetricProductDecodeBHist (completeMetricProductEncodeBHist LY))
            (completeMetricProductDecodeBHist (completeMetricProductEncodeBHist Pi))
            (completeMetricProductDecodeBHist (completeMetricProductEncodeBHist L))
            (completeMetricProductDecodeBHist (completeMetricProductEncodeBHist H))
            (completeMetricProductDecodeBHist (completeMetricProductEncodeBHist C))
            (completeMetricProductDecodeBHist (completeMetricProductEncodeBHist P))
            (completeMetricProductDecodeBHist (completeMetricProductEncodeBHist N))) =
          some (CompleteMetricProductUp.mk M X Y SX SY RX RY AX AY LX LY Pi L H C P N)
      rw [CompleteMetricProductTasteGate_single_carrier_alignment_decode M,
        CompleteMetricProductTasteGate_single_carrier_alignment_decode X,
        CompleteMetricProductTasteGate_single_carrier_alignment_decode Y,
        CompleteMetricProductTasteGate_single_carrier_alignment_decode SX,
        CompleteMetricProductTasteGate_single_carrier_alignment_decode SY,
        CompleteMetricProductTasteGate_single_carrier_alignment_decode RX,
        CompleteMetricProductTasteGate_single_carrier_alignment_decode RY,
        CompleteMetricProductTasteGate_single_carrier_alignment_decode AX,
        CompleteMetricProductTasteGate_single_carrier_alignment_decode AY,
        CompleteMetricProductTasteGate_single_carrier_alignment_decode LX,
        CompleteMetricProductTasteGate_single_carrier_alignment_decode LY,
        CompleteMetricProductTasteGate_single_carrier_alignment_decode Pi,
        CompleteMetricProductTasteGate_single_carrier_alignment_decode L,
        CompleteMetricProductTasteGate_single_carrier_alignment_decode H,
        CompleteMetricProductTasteGate_single_carrier_alignment_decode C,
        CompleteMetricProductTasteGate_single_carrier_alignment_decode P,
        CompleteMetricProductTasteGate_single_carrier_alignment_decode N]

private theorem CompleteMetricProductTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompleteMetricProductUp} :
    completeMetricProductToEventFlow x = completeMetricProductToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      completeMetricProductFromEventFlow (completeMetricProductToEventFlow x) =
        completeMetricProductFromEventFlow (completeMetricProductToEventFlow y) :=
    congrArg completeMetricProductFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompleteMetricProductTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CompleteMetricProductTasteGate_single_carrier_alignment_round_trip y)))

private theorem CompleteMetricProductTasteGate_single_carrier_alignment_fields :
    ∀ x y : CompleteMetricProductUp, completeMetricProductFields x =
      completeMetricProductFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 X1 Y1 SX1 SY1 RX1 RY1 AX1 AY1 LX1 LY1 Pi1 L1 H1 C1 P1 N1 =>
      cases y with
      | mk M2 X2 Y2 SX2 SY2 RX2 RY2 AX2 AY2 LX2 LY2 Pi2 L2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance completeMetricProductBHistCarrier : BHistCarrier CompleteMetricProductUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := completeMetricProductToEventFlow
  fromEventFlow := completeMetricProductFromEventFlow

instance completeMetricProductChapterTasteGate : ChapterTasteGate CompleteMetricProductUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change completeMetricProductFromEventFlow (completeMetricProductToEventFlow x) = some x
    exact CompleteMetricProductTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompleteMetricProductTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance completeMetricProductFieldFaithful : FieldFaithful CompleteMetricProductUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := completeMetricProductFields
  field_faithful := CompleteMetricProductTasteGate_single_carrier_alignment_fields

instance completeMetricProductNontrivial : Nontrivial CompleteMetricProductUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompleteMetricProductUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CompleteMetricProductUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CompleteMetricProductUp :=
  -- BEDC touchpoint anchor: BHist BMark
  completeMetricProductChapterTasteGate

theorem CompleteMetricProductTasteGate_single_carrier_alignment :
    (∀ h : BHist, completeMetricProductDecodeBHist
        (completeMetricProductEncodeBHist h) = h) ∧
      (∀ x : CompleteMetricProductUp,
        completeMetricProductFromEventFlow (completeMetricProductToEventFlow x) = some x) ∧
        (∀ x y : CompleteMetricProductUp,
          completeMetricProductToEventFlow x = completeMetricProductToEventFlow y → x = y) ∧
          completeMetricProductEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨CompleteMetricProductTasteGate_single_carrier_alignment_decode,
      CompleteMetricProductTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CompleteMetricProductTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CompleteMetricProductUp
