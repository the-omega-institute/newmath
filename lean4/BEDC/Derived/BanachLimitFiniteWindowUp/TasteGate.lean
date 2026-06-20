import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BanachLimitFiniteWindowUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BanachLimitFiniteWindowUp : Type where
  | mk (B S A H T V E M C P N : BHist) : BanachLimitFiniteWindowUp
  deriving DecidableEq

instance banachLimitFiniteWindowInhabited : Inhabited BanachLimitFiniteWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  default :=
    BanachLimitFiniteWindowUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty

def banachLimitFiniteWindowEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: banachLimitFiniteWindowEncodeBHist h
  | BHist.e1 h => BMark.b1 :: banachLimitFiniteWindowEncodeBHist h

def banachLimitFiniteWindowDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (banachLimitFiniteWindowDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (banachLimitFiniteWindowDecodeBHist tail)

private theorem BanachLimitFiniteWindowTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, banachLimitFiniteWindowDecodeBHist
      (banachLimitFiniteWindowEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def banachLimitFiniteWindowFields : BanachLimitFiniteWindowUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BanachLimitFiniteWindowUp.mk B S A H T V E M C P N => [B, S, A, H, T, V, E, M, C, P, N]

def banachLimitFiniteWindowToEventFlow : BanachLimitFiniteWindowUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (banachLimitFiniteWindowFields x).map banachLimitFiniteWindowEncodeBHist

private def banachLimitFiniteWindowEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => banachLimitFiniteWindowEventAtDefault index rest

def banachLimitFiniteWindowFromEventFlow (ef : EventFlow) : Option BanachLimitFiniteWindowUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BanachLimitFiniteWindowUp.mk
      (banachLimitFiniteWindowDecodeBHist (banachLimitFiniteWindowEventAtDefault 0 ef))
      (banachLimitFiniteWindowDecodeBHist (banachLimitFiniteWindowEventAtDefault 1 ef))
      (banachLimitFiniteWindowDecodeBHist (banachLimitFiniteWindowEventAtDefault 2 ef))
      (banachLimitFiniteWindowDecodeBHist (banachLimitFiniteWindowEventAtDefault 3 ef))
      (banachLimitFiniteWindowDecodeBHist (banachLimitFiniteWindowEventAtDefault 4 ef))
      (banachLimitFiniteWindowDecodeBHist (banachLimitFiniteWindowEventAtDefault 5 ef))
      (banachLimitFiniteWindowDecodeBHist (banachLimitFiniteWindowEventAtDefault 6 ef))
      (banachLimitFiniteWindowDecodeBHist (banachLimitFiniteWindowEventAtDefault 7 ef))
      (banachLimitFiniteWindowDecodeBHist (banachLimitFiniteWindowEventAtDefault 8 ef))
      (banachLimitFiniteWindowDecodeBHist (banachLimitFiniteWindowEventAtDefault 9 ef))
      (banachLimitFiniteWindowDecodeBHist (banachLimitFiniteWindowEventAtDefault 10 ef)))

private theorem BanachLimitFiniteWindowTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BanachLimitFiniteWindowUp,
      banachLimitFiniteWindowFromEventFlow (banachLimitFiniteWindowToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B S A H T V E M C P N =>
      change
        some
          (BanachLimitFiniteWindowUp.mk
            (banachLimitFiniteWindowDecodeBHist (banachLimitFiniteWindowEncodeBHist B))
            (banachLimitFiniteWindowDecodeBHist (banachLimitFiniteWindowEncodeBHist S))
            (banachLimitFiniteWindowDecodeBHist (banachLimitFiniteWindowEncodeBHist A))
            (banachLimitFiniteWindowDecodeBHist (banachLimitFiniteWindowEncodeBHist H))
            (banachLimitFiniteWindowDecodeBHist (banachLimitFiniteWindowEncodeBHist T))
            (banachLimitFiniteWindowDecodeBHist (banachLimitFiniteWindowEncodeBHist V))
            (banachLimitFiniteWindowDecodeBHist (banachLimitFiniteWindowEncodeBHist E))
            (banachLimitFiniteWindowDecodeBHist (banachLimitFiniteWindowEncodeBHist M))
            (banachLimitFiniteWindowDecodeBHist (banachLimitFiniteWindowEncodeBHist C))
            (banachLimitFiniteWindowDecodeBHist (banachLimitFiniteWindowEncodeBHist P))
            (banachLimitFiniteWindowDecodeBHist (banachLimitFiniteWindowEncodeBHist N))) =
          some (BanachLimitFiniteWindowUp.mk B S A H T V E M C P N)
      rw [BanachLimitFiniteWindowTasteGate_single_carrier_alignment_decode B,
        BanachLimitFiniteWindowTasteGate_single_carrier_alignment_decode S,
        BanachLimitFiniteWindowTasteGate_single_carrier_alignment_decode A,
        BanachLimitFiniteWindowTasteGate_single_carrier_alignment_decode H,
        BanachLimitFiniteWindowTasteGate_single_carrier_alignment_decode T,
        BanachLimitFiniteWindowTasteGate_single_carrier_alignment_decode V,
        BanachLimitFiniteWindowTasteGate_single_carrier_alignment_decode E,
        BanachLimitFiniteWindowTasteGate_single_carrier_alignment_decode M,
        BanachLimitFiniteWindowTasteGate_single_carrier_alignment_decode C,
        BanachLimitFiniteWindowTasteGate_single_carrier_alignment_decode P,
        BanachLimitFiniteWindowTasteGate_single_carrier_alignment_decode N]

private theorem BanachLimitFiniteWindowToEventFlow_injective {x y : BanachLimitFiniteWindowUp} :
    banachLimitFiniteWindowToEventFlow x = banachLimitFiniteWindowToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      banachLimitFiniteWindowFromEventFlow (banachLimitFiniteWindowToEventFlow x) =
        banachLimitFiniteWindowFromEventFlow (banachLimitFiniteWindowToEventFlow y) :=
    congrArg banachLimitFiniteWindowFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BanachLimitFiniteWindowTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BanachLimitFiniteWindowTasteGate_single_carrier_alignment_round_trip y)))

private theorem BanachLimitFiniteWindowTasteGate_single_carrier_alignment_fields :
    ∀ x y : BanachLimitFiniteWindowUp,
      banachLimitFiniteWindowFields x = banachLimitFiniteWindowFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B1 S1 A1 H1 T1 V1 E1 M1 C1 P1 N1 =>
      cases y with
      | mk B2 S2 A2 H2 T2 V2 E2 M2 C2 P2 N2 =>
          cases hfields
          rfl

instance banachLimitFiniteWindowBHistCarrier : BHistCarrier BanachLimitFiniteWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := banachLimitFiniteWindowToEventFlow
  fromEventFlow := banachLimitFiniteWindowFromEventFlow

instance banachLimitFiniteWindowChapterTasteGate : ChapterTasteGate BanachLimitFiniteWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change banachLimitFiniteWindowFromEventFlow (banachLimitFiniteWindowToEventFlow x) = some x
    exact BanachLimitFiniteWindowTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BanachLimitFiniteWindowToEventFlow_injective heq)

instance banachLimitFiniteWindowFieldFaithful : FieldFaithful BanachLimitFiniteWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := banachLimitFiniteWindowFields
  field_faithful := BanachLimitFiniteWindowTasteGate_single_carrier_alignment_fields

theorem BanachLimitFiniteWindowTasteGate_single_carrier_alignment :
    (∀ h : BHist, banachLimitFiniteWindowDecodeBHist
      (banachLimitFiniteWindowEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BanachLimitFiniteWindowUp) ∧
        Nonempty (ChapterTasteGate BanachLimitFiniteWindowUp) ∧
          FieldFaithful.field_count BanachLimitFiniteWindowUp = 11 ∧
            banachLimitFiniteWindowToEventFlow
                (BanachLimitFiniteWindowUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty) ≠
              banachLimitFiniteWindowToEventFlow
                (BanachLimitFiniteWindowUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨BanachLimitFiniteWindowTasteGate_single_carrier_alignment_decode,
      ⟨banachLimitFiniteWindowBHistCarrier⟩,
      ⟨banachLimitFiniteWindowChapterTasteGate⟩,
      rfl,
      by
        intro h
        injection h with hhead _tail
        cases hhead⟩

end BEDC.Derived.BanachLimitFiniteWindowUp
