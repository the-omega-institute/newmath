import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyModulusBridgeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyModulusBridgeUp : Type where
  | mk (Q M E S D R L H C P N : BHist) : CauchyModulusBridgeUp
  deriving DecidableEq

def cauchyModulusBridgeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyModulusBridgeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyModulusBridgeEncodeBHist h

def cauchyModulusBridgeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyModulusBridgeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyModulusBridgeDecodeBHist tail)

private theorem CauchyModulusBridgeTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cauchyModulusBridgeDecodeBHist (cauchyModulusBridgeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyModulusBridgeFields : CauchyModulusBridgeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyModulusBridgeUp.mk Q M E S D R L H C P N => [Q, M, E, S, D, R, L, H, C, P, N]

def cauchyModulusBridgeToEventFlow : CauchyModulusBridgeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyModulusBridgeFields x).map cauchyModulusBridgeEncodeBHist

private def cauchyModulusBridgeEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyModulusBridgeEventAt index rest

def cauchyModulusBridgeFromEventFlow : EventFlow → Option CauchyModulusBridgeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CauchyModulusBridgeUp.mk
        (cauchyModulusBridgeDecodeBHist (cauchyModulusBridgeEventAt 0 ef))
        (cauchyModulusBridgeDecodeBHist (cauchyModulusBridgeEventAt 1 ef))
        (cauchyModulusBridgeDecodeBHist (cauchyModulusBridgeEventAt 2 ef))
        (cauchyModulusBridgeDecodeBHist (cauchyModulusBridgeEventAt 3 ef))
        (cauchyModulusBridgeDecodeBHist (cauchyModulusBridgeEventAt 4 ef))
        (cauchyModulusBridgeDecodeBHist (cauchyModulusBridgeEventAt 5 ef))
        (cauchyModulusBridgeDecodeBHist (cauchyModulusBridgeEventAt 6 ef))
        (cauchyModulusBridgeDecodeBHist (cauchyModulusBridgeEventAt 7 ef))
        (cauchyModulusBridgeDecodeBHist (cauchyModulusBridgeEventAt 8 ef))
        (cauchyModulusBridgeDecodeBHist (cauchyModulusBridgeEventAt 9 ef))
        (cauchyModulusBridgeDecodeBHist (cauchyModulusBridgeEventAt 10 ef)))

private theorem cauchyModulusBridge_round_trip :
    ∀ x : CauchyModulusBridgeUp,
      cauchyModulusBridgeFromEventFlow (cauchyModulusBridgeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q M E S D R L H C P N =>
      change
        some
          (CauchyModulusBridgeUp.mk
            (cauchyModulusBridgeDecodeBHist (cauchyModulusBridgeEncodeBHist Q))
            (cauchyModulusBridgeDecodeBHist (cauchyModulusBridgeEncodeBHist M))
            (cauchyModulusBridgeDecodeBHist (cauchyModulusBridgeEncodeBHist E))
            (cauchyModulusBridgeDecodeBHist (cauchyModulusBridgeEncodeBHist S))
            (cauchyModulusBridgeDecodeBHist (cauchyModulusBridgeEncodeBHist D))
            (cauchyModulusBridgeDecodeBHist (cauchyModulusBridgeEncodeBHist R))
            (cauchyModulusBridgeDecodeBHist (cauchyModulusBridgeEncodeBHist L))
            (cauchyModulusBridgeDecodeBHist (cauchyModulusBridgeEncodeBHist H))
            (cauchyModulusBridgeDecodeBHist (cauchyModulusBridgeEncodeBHist C))
            (cauchyModulusBridgeDecodeBHist (cauchyModulusBridgeEncodeBHist P))
            (cauchyModulusBridgeDecodeBHist (cauchyModulusBridgeEncodeBHist N))) =
          some (CauchyModulusBridgeUp.mk Q M E S D R L H C P N)
      rw [CauchyModulusBridgeTasteGate_single_carrier_alignment_decode_encode Q,
        CauchyModulusBridgeTasteGate_single_carrier_alignment_decode_encode M,
        CauchyModulusBridgeTasteGate_single_carrier_alignment_decode_encode E,
        CauchyModulusBridgeTasteGate_single_carrier_alignment_decode_encode S,
        CauchyModulusBridgeTasteGate_single_carrier_alignment_decode_encode D,
        CauchyModulusBridgeTasteGate_single_carrier_alignment_decode_encode R,
        CauchyModulusBridgeTasteGate_single_carrier_alignment_decode_encode L,
        CauchyModulusBridgeTasteGate_single_carrier_alignment_decode_encode H,
        CauchyModulusBridgeTasteGate_single_carrier_alignment_decode_encode C,
        CauchyModulusBridgeTasteGate_single_carrier_alignment_decode_encode P,
        CauchyModulusBridgeTasteGate_single_carrier_alignment_decode_encode N]

private theorem cauchyModulusBridgeToEventFlow_injective {x y : CauchyModulusBridgeUp} :
    cauchyModulusBridgeToEventFlow x = cauchyModulusBridgeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyModulusBridgeFromEventFlow (cauchyModulusBridgeToEventFlow x) =
        cauchyModulusBridgeFromEventFlow (cauchyModulusBridgeToEventFlow y) :=
    congrArg cauchyModulusBridgeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyModulusBridge_round_trip x).symm
      (Eq.trans hread (cauchyModulusBridge_round_trip y)))

private theorem cauchyModulusBridge_field_faithful :
    ∀ x y : CauchyModulusBridgeUp,
      cauchyModulusBridgeFields x = cauchyModulusBridgeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk Q1 M1 E1 S1 D1 R1 L1 H1 C1 P1 N1 =>
      cases y with
      | mk Q2 M2 E2 S2 D2 R2 L2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance cauchyModulusBridgeBHistCarrier : BHistCarrier CauchyModulusBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyModulusBridgeToEventFlow
  fromEventFlow := cauchyModulusBridgeFromEventFlow

instance cauchyModulusBridgeChapterTasteGate : ChapterTasteGate CauchyModulusBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyModulusBridgeFromEventFlow (cauchyModulusBridgeToEventFlow x) = some x
    exact cauchyModulusBridge_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyModulusBridgeToEventFlow_injective heq)

instance cauchyModulusBridgeFieldFaithful : FieldFaithful CauchyModulusBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyModulusBridgeFields
  field_faithful := cauchyModulusBridge_field_faithful

instance cauchyModulusBridgeNontrivial : Nontrivial CauchyModulusBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyModulusBridgeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyModulusBridgeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CauchyModulusBridgeTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchyModulusBridgeUp) ∧
      Nonempty (FieldFaithful CauchyModulusBridgeUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial CauchyModulusBridgeUp) ∧
          (∀ h : BHist,
            cauchyModulusBridgeDecodeBHist (cauchyModulusBridgeEncodeBHist h) = h) ∧
            (∀ x : CauchyModulusBridgeUp,
              cauchyModulusBridgeFromEventFlow
                (cauchyModulusBridgeToEventFlow x) = some x) ∧
              (∀ x y : CauchyModulusBridgeUp,
                cauchyModulusBridgeToEventFlow x =
                  cauchyModulusBridgeToEventFlow y → x = y) ∧
                cauchyModulusBridgeEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact ⟨cauchyModulusBridgeChapterTasteGate⟩
  constructor
  · exact ⟨cauchyModulusBridgeFieldFaithful⟩
  constructor
  · exact ⟨cauchyModulusBridgeNontrivial⟩
  constructor
  · exact CauchyModulusBridgeTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact cauchyModulusBridge_round_trip
  constructor
  · intro x y heq
    exact cauchyModulusBridgeToEventFlow_injective heq
  · rfl

end BEDC.Derived.CauchyModulusBridgeUp
