import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactUniformRadiusTransportUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactUniformRadiusTransportUp : Type where
  | mk (K M F R U H C P N : BHist) : CompactUniformRadiusTransportUp
  deriving DecidableEq

def compactUniformRadiusTransportEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactUniformRadiusTransportEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactUniformRadiusTransportEncodeBHist h

def compactUniformRadiusTransportDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactUniformRadiusTransportDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactUniformRadiusTransportDecodeBHist tail)

private theorem CompactUniformRadiusTransportTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      compactUniformRadiusTransportDecodeBHist
        (compactUniformRadiusTransportEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactUniformRadiusTransportFields : CompactUniformRadiusTransportUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactUniformRadiusTransportUp.mk K M F R U H C P N => [K, M, F, R, U, H, C, P, N]

def compactUniformRadiusTransportToEventFlow : CompactUniformRadiusTransportUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactUniformRadiusTransportFields x).map compactUniformRadiusTransportEncodeBHist

private def compactUniformRadiusTransportEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compactUniformRadiusTransportEventAtDefault index rest

def compactUniformRadiusTransportFromEventFlow
    (ef : EventFlow) : Option CompactUniformRadiusTransportUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactUniformRadiusTransportUp.mk
      (compactUniformRadiusTransportDecodeBHist (compactUniformRadiusTransportEventAtDefault 0 ef))
      (compactUniformRadiusTransportDecodeBHist (compactUniformRadiusTransportEventAtDefault 1 ef))
      (compactUniformRadiusTransportDecodeBHist (compactUniformRadiusTransportEventAtDefault 2 ef))
      (compactUniformRadiusTransportDecodeBHist (compactUniformRadiusTransportEventAtDefault 3 ef))
      (compactUniformRadiusTransportDecodeBHist (compactUniformRadiusTransportEventAtDefault 4 ef))
      (compactUniformRadiusTransportDecodeBHist (compactUniformRadiusTransportEventAtDefault 5 ef))
      (compactUniformRadiusTransportDecodeBHist (compactUniformRadiusTransportEventAtDefault 6 ef))
      (compactUniformRadiusTransportDecodeBHist (compactUniformRadiusTransportEventAtDefault 7 ef))
      (compactUniformRadiusTransportDecodeBHist (compactUniformRadiusTransportEventAtDefault 8 ef)))

private theorem CompactUniformRadiusTransportTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompactUniformRadiusTransportUp,
      compactUniformRadiusTransportFromEventFlow
        (compactUniformRadiusTransportToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K M F R U H C P N =>
      change
        some
          (CompactUniformRadiusTransportUp.mk
            (compactUniformRadiusTransportDecodeBHist
              (compactUniformRadiusTransportEncodeBHist K))
            (compactUniformRadiusTransportDecodeBHist
              (compactUniformRadiusTransportEncodeBHist M))
            (compactUniformRadiusTransportDecodeBHist
              (compactUniformRadiusTransportEncodeBHist F))
            (compactUniformRadiusTransportDecodeBHist
              (compactUniformRadiusTransportEncodeBHist R))
            (compactUniformRadiusTransportDecodeBHist
              (compactUniformRadiusTransportEncodeBHist U))
            (compactUniformRadiusTransportDecodeBHist
              (compactUniformRadiusTransportEncodeBHist H))
            (compactUniformRadiusTransportDecodeBHist
              (compactUniformRadiusTransportEncodeBHist C))
            (compactUniformRadiusTransportDecodeBHist
              (compactUniformRadiusTransportEncodeBHist P))
            (compactUniformRadiusTransportDecodeBHist
              (compactUniformRadiusTransportEncodeBHist N))) =
          some (CompactUniformRadiusTransportUp.mk K M F R U H C P N)
      rw [CompactUniformRadiusTransportTasteGate_single_carrier_alignment_decode K,
        CompactUniformRadiusTransportTasteGate_single_carrier_alignment_decode M,
        CompactUniformRadiusTransportTasteGate_single_carrier_alignment_decode F,
        CompactUniformRadiusTransportTasteGate_single_carrier_alignment_decode R,
        CompactUniformRadiusTransportTasteGate_single_carrier_alignment_decode U,
        CompactUniformRadiusTransportTasteGate_single_carrier_alignment_decode H,
        CompactUniformRadiusTransportTasteGate_single_carrier_alignment_decode C,
        CompactUniformRadiusTransportTasteGate_single_carrier_alignment_decode P,
        CompactUniformRadiusTransportTasteGate_single_carrier_alignment_decode N]

private theorem CompactUniformRadiusTransportTasteGate_single_carrier_alignment_injective
    {x y : CompactUniformRadiusTransportUp} :
    compactUniformRadiusTransportToEventFlow x =
      compactUniformRadiusTransportToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactUniformRadiusTransportFromEventFlow
          (compactUniformRadiusTransportToEventFlow x) =
        compactUniformRadiusTransportFromEventFlow
          (compactUniformRadiusTransportToEventFlow y) :=
    congrArg compactUniformRadiusTransportFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompactUniformRadiusTransportTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactUniformRadiusTransportTasteGate_single_carrier_alignment_round_trip y)))

private theorem CompactUniformRadiusTransportTasteGate_single_carrier_alignment_fields :
    ∀ x y : CompactUniformRadiusTransportUp,
      compactUniformRadiusTransportFields x = compactUniformRadiusTransportFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K1 M1 F1 R1 U1 H1 C1 P1 N1 =>
      cases y with
      | mk K2 M2 F2 R2 U2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance compactUniformRadiusTransportBHistCarrier :
    BHistCarrier CompactUniformRadiusTransportUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactUniformRadiusTransportToEventFlow
  fromEventFlow := compactUniformRadiusTransportFromEventFlow

instance compactUniformRadiusTransportChapterTasteGate :
    ChapterTasteGate CompactUniformRadiusTransportUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactUniformRadiusTransportFromEventFlow
        (compactUniformRadiusTransportToEventFlow x) = some x
    exact CompactUniformRadiusTransportTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompactUniformRadiusTransportTasteGate_single_carrier_alignment_injective heq)

instance compactUniformRadiusTransportFieldFaithful :
    FieldFaithful CompactUniformRadiusTransportUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactUniformRadiusTransportFields
  field_faithful := CompactUniformRadiusTransportTasteGate_single_carrier_alignment_fields

instance compactUniformRadiusTransportNontrivial :
    Nontrivial CompactUniformRadiusTransportUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompactUniformRadiusTransportUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CompactUniformRadiusTransportUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CompactUniformRadiusTransportTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CompactUniformRadiusTransportUp) ∧
      Nonempty (FieldFaithful CompactUniformRadiusTransportUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial CompactUniformRadiusTransportUp) ∧
          (∀ h : BHist,
            compactUniformRadiusTransportDecodeBHist
              (compactUniformRadiusTransportEncodeBHist h) = h) ∧
            compactUniformRadiusTransportEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] ∧
              (∀ x : CompactUniformRadiusTransportUp,
                compactUniformRadiusTransportFromEventFlow
                  (compactUniformRadiusTransportToEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨compactUniformRadiusTransportChapterTasteGate⟩,
      ⟨compactUniformRadiusTransportFieldFaithful⟩,
      ⟨compactUniformRadiusTransportNontrivial⟩,
      CompactUniformRadiusTransportTasteGate_single_carrier_alignment_decode,
      rfl,
      CompactUniformRadiusTransportTasteGate_single_carrier_alignment_round_trip⟩

end BEDC.Derived.CompactUniformRadiusTransportUp
