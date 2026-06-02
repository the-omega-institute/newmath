import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyDedekindBridgeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyDedekindBridgeUp : Type where
  | mk (R W D L B E H C P N : BHist) : CauchyDedekindBridgeUp
  deriving DecidableEq

def cauchyDedekindBridgeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyDedekindBridgeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyDedekindBridgeEncodeBHist h

def cauchyDedekindBridgeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyDedekindBridgeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyDedekindBridgeDecodeBHist tail)

private theorem CauchyDedekindBridgeTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyDedekindBridgeDecodeBHist (cauchyDedekindBridgeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyDedekindBridgeFields : CauchyDedekindBridgeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyDedekindBridgeUp.mk R W D L B E H C P N => [R, W, D, L, B, E, H, C, P, N]

def cauchyDedekindBridgeToEventFlow : CauchyDedekindBridgeUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cauchyDedekindBridgeFields x).map cauchyDedekindBridgeEncodeBHist

private def cauchyDedekindBridgeEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyDedekindBridgeEventAtDefault index rest

def cauchyDedekindBridgeFromEventFlow (ef : EventFlow) : Option CauchyDedekindBridgeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyDedekindBridgeUp.mk
      (cauchyDedekindBridgeDecodeBHist (cauchyDedekindBridgeEventAtDefault 0 ef))
      (cauchyDedekindBridgeDecodeBHist (cauchyDedekindBridgeEventAtDefault 1 ef))
      (cauchyDedekindBridgeDecodeBHist (cauchyDedekindBridgeEventAtDefault 2 ef))
      (cauchyDedekindBridgeDecodeBHist (cauchyDedekindBridgeEventAtDefault 3 ef))
      (cauchyDedekindBridgeDecodeBHist (cauchyDedekindBridgeEventAtDefault 4 ef))
      (cauchyDedekindBridgeDecodeBHist (cauchyDedekindBridgeEventAtDefault 5 ef))
      (cauchyDedekindBridgeDecodeBHist (cauchyDedekindBridgeEventAtDefault 6 ef))
      (cauchyDedekindBridgeDecodeBHist (cauchyDedekindBridgeEventAtDefault 7 ef))
      (cauchyDedekindBridgeDecodeBHist (cauchyDedekindBridgeEventAtDefault 8 ef))
      (cauchyDedekindBridgeDecodeBHist (cauchyDedekindBridgeEventAtDefault 9 ef)))

private theorem CauchyDedekindBridgeTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyDedekindBridgeUp,
      cauchyDedekindBridgeFromEventFlow (cauchyDedekindBridgeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R W D L B E H C P N =>
      change
        some
          (CauchyDedekindBridgeUp.mk
            (cauchyDedekindBridgeDecodeBHist (cauchyDedekindBridgeEncodeBHist R))
            (cauchyDedekindBridgeDecodeBHist (cauchyDedekindBridgeEncodeBHist W))
            (cauchyDedekindBridgeDecodeBHist (cauchyDedekindBridgeEncodeBHist D))
            (cauchyDedekindBridgeDecodeBHist (cauchyDedekindBridgeEncodeBHist L))
            (cauchyDedekindBridgeDecodeBHist (cauchyDedekindBridgeEncodeBHist B))
            (cauchyDedekindBridgeDecodeBHist (cauchyDedekindBridgeEncodeBHist E))
            (cauchyDedekindBridgeDecodeBHist (cauchyDedekindBridgeEncodeBHist H))
            (cauchyDedekindBridgeDecodeBHist (cauchyDedekindBridgeEncodeBHist C))
            (cauchyDedekindBridgeDecodeBHist (cauchyDedekindBridgeEncodeBHist P))
            (cauchyDedekindBridgeDecodeBHist (cauchyDedekindBridgeEncodeBHist N))) =
          some (CauchyDedekindBridgeUp.mk R W D L B E H C P N)
      rw [CauchyDedekindBridgeTasteGate_single_carrier_alignment_decode R,
        CauchyDedekindBridgeTasteGate_single_carrier_alignment_decode W,
        CauchyDedekindBridgeTasteGate_single_carrier_alignment_decode D,
        CauchyDedekindBridgeTasteGate_single_carrier_alignment_decode L,
        CauchyDedekindBridgeTasteGate_single_carrier_alignment_decode B,
        CauchyDedekindBridgeTasteGate_single_carrier_alignment_decode E,
        CauchyDedekindBridgeTasteGate_single_carrier_alignment_decode H,
        CauchyDedekindBridgeTasteGate_single_carrier_alignment_decode C,
        CauchyDedekindBridgeTasteGate_single_carrier_alignment_decode P,
        CauchyDedekindBridgeTasteGate_single_carrier_alignment_decode N]

private theorem CauchyDedekindBridgeTasteGate_single_carrier_alignment_injective
    {x y : CauchyDedekindBridgeUp} :
    cauchyDedekindBridgeToEventFlow x = cauchyDedekindBridgeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyDedekindBridgeFromEventFlow (cauchyDedekindBridgeToEventFlow x) =
        cauchyDedekindBridgeFromEventFlow (cauchyDedekindBridgeToEventFlow y) :=
    congrArg cauchyDedekindBridgeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyDedekindBridgeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyDedekindBridgeTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyDedekindBridgeTasteGate_single_carrier_alignment_fields :
    ∀ x y : CauchyDedekindBridgeUp,
      cauchyDedekindBridgeFields x = cauchyDedekindBridgeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R1 W1 D1 L1 B1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk R2 W2 D2 L2 B2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance cauchyDedekindBridgeBHistCarrier : BHistCarrier CauchyDedekindBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyDedekindBridgeToEventFlow
  fromEventFlow := cauchyDedekindBridgeFromEventFlow

instance cauchyDedekindBridgeChapterTasteGate : ChapterTasteGate CauchyDedekindBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyDedekindBridgeFromEventFlow (cauchyDedekindBridgeToEventFlow x) = some x
    exact CauchyDedekindBridgeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyDedekindBridgeTasteGate_single_carrier_alignment_injective heq)

instance cauchyDedekindBridgeFieldFaithful : FieldFaithful CauchyDedekindBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyDedekindBridgeFields
  field_faithful := CauchyDedekindBridgeTasteGate_single_carrier_alignment_fields

instance cauchyDedekindBridgeNontrivial : Nontrivial CauchyDedekindBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyDedekindBridgeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyDedekindBridgeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyDedekindBridgeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyDedekindBridgeChapterTasteGate

theorem CauchyDedekindBridgeTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyDedekindBridgeDecodeBHist (cauchyDedekindBridgeEncodeBHist h) = h) ∧
      (∀ x : CauchyDedekindBridgeUp,
        cauchyDedekindBridgeFromEventFlow (cauchyDedekindBridgeToEventFlow x) =
          some x) ∧
        (∀ x y : CauchyDedekindBridgeUp,
          cauchyDedekindBridgeToEventFlow x = cauchyDedekindBridgeToEventFlow y →
            x = y) ∧
          cauchyDedekindBridgeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨CauchyDedekindBridgeTasteGate_single_carrier_alignment_decode,
      CauchyDedekindBridgeTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => CauchyDedekindBridgeTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.CauchyDedekindBridgeUp
