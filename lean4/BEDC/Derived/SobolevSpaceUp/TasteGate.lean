import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SobolevSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SobolevSpaceUp : Type where
  | mk (F D N0 I M R H C P L : BHist) : SobolevSpaceUp
  deriving DecidableEq

def sobolevSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sobolevSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sobolevSpaceEncodeBHist h

def sobolevSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sobolevSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sobolevSpaceDecodeBHist tail)

private theorem SobolevSpaceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, sobolevSpaceDecodeBHist (sobolevSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sobolevSpaceFields : SobolevSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SobolevSpaceUp.mk F D N0 I M R H C P L => [F, D, N0, I, M, R, H, C, P, L]

def sobolevSpaceToEventFlow : SobolevSpaceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (sobolevSpaceFields x).map sobolevSpaceEncodeBHist

private def sobolevSpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => sobolevSpaceEventAtDefault index rest

def sobolevSpaceFromEventFlow (ef : EventFlow) : Option SobolevSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SobolevSpaceUp.mk
      (sobolevSpaceDecodeBHist (sobolevSpaceEventAtDefault 0 ef))
      (sobolevSpaceDecodeBHist (sobolevSpaceEventAtDefault 1 ef))
      (sobolevSpaceDecodeBHist (sobolevSpaceEventAtDefault 2 ef))
      (sobolevSpaceDecodeBHist (sobolevSpaceEventAtDefault 3 ef))
      (sobolevSpaceDecodeBHist (sobolevSpaceEventAtDefault 4 ef))
      (sobolevSpaceDecodeBHist (sobolevSpaceEventAtDefault 5 ef))
      (sobolevSpaceDecodeBHist (sobolevSpaceEventAtDefault 6 ef))
      (sobolevSpaceDecodeBHist (sobolevSpaceEventAtDefault 7 ef))
      (sobolevSpaceDecodeBHist (sobolevSpaceEventAtDefault 8 ef))
      (sobolevSpaceDecodeBHist (sobolevSpaceEventAtDefault 9 ef)))

private theorem SobolevSpaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SobolevSpaceUp,
      sobolevSpaceFromEventFlow (sobolevSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F D N0 I M R H C P L =>
      change
        some
          (SobolevSpaceUp.mk
            (sobolevSpaceDecodeBHist (sobolevSpaceEncodeBHist F))
            (sobolevSpaceDecodeBHist (sobolevSpaceEncodeBHist D))
            (sobolevSpaceDecodeBHist (sobolevSpaceEncodeBHist N0))
            (sobolevSpaceDecodeBHist (sobolevSpaceEncodeBHist I))
            (sobolevSpaceDecodeBHist (sobolevSpaceEncodeBHist M))
            (sobolevSpaceDecodeBHist (sobolevSpaceEncodeBHist R))
            (sobolevSpaceDecodeBHist (sobolevSpaceEncodeBHist H))
            (sobolevSpaceDecodeBHist (sobolevSpaceEncodeBHist C))
            (sobolevSpaceDecodeBHist (sobolevSpaceEncodeBHist P))
            (sobolevSpaceDecodeBHist (sobolevSpaceEncodeBHist L))) =
          some (SobolevSpaceUp.mk F D N0 I M R H C P L)
      rw [SobolevSpaceTasteGate_single_carrier_alignment_decode F,
        SobolevSpaceTasteGate_single_carrier_alignment_decode D,
        SobolevSpaceTasteGate_single_carrier_alignment_decode N0,
        SobolevSpaceTasteGate_single_carrier_alignment_decode I,
        SobolevSpaceTasteGate_single_carrier_alignment_decode M,
        SobolevSpaceTasteGate_single_carrier_alignment_decode R,
        SobolevSpaceTasteGate_single_carrier_alignment_decode H,
        SobolevSpaceTasteGate_single_carrier_alignment_decode C,
        SobolevSpaceTasteGate_single_carrier_alignment_decode P,
        SobolevSpaceTasteGate_single_carrier_alignment_decode L]

private theorem SobolevSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SobolevSpaceUp} :
    sobolevSpaceToEventFlow x = sobolevSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sobolevSpaceFromEventFlow (sobolevSpaceToEventFlow x) =
        sobolevSpaceFromEventFlow (sobolevSpaceToEventFlow y) :=
    congrArg sobolevSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SobolevSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SobolevSpaceTasteGate_single_carrier_alignment_round_trip y)))

private theorem SobolevSpaceTasteGate_single_carrier_alignment_fields :
    ∀ x y : SobolevSpaceUp, sobolevSpaceFields x = sobolevSpaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F1 D1 N01 I1 M1 R1 H1 C1 P1 L1 =>
      cases y with
      | mk F2 D2 N02 I2 M2 R2 H2 C2 P2 L2 =>
          cases hfields
          rfl

instance sobolevSpaceBHistCarrier : BHistCarrier SobolevSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sobolevSpaceToEventFlow
  fromEventFlow := sobolevSpaceFromEventFlow

instance sobolevSpaceChapterTasteGate : ChapterTasteGate SobolevSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sobolevSpaceFromEventFlow (sobolevSpaceToEventFlow x) = some x
    exact SobolevSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SobolevSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance sobolevSpaceFieldFaithful : FieldFaithful SobolevSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := sobolevSpaceFields
  field_faithful := SobolevSpaceTasteGate_single_carrier_alignment_fields

instance sobolevSpaceNontrivial : Nontrivial SobolevSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SobolevSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SobolevSpaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SobolevSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  sobolevSpaceChapterTasteGate

theorem SobolevSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, sobolevSpaceDecodeBHist (sobolevSpaceEncodeBHist h) = h) ∧
      (∀ x : SobolevSpaceUp,
        sobolevSpaceFromEventFlow (sobolevSpaceToEventFlow x) = some x) ∧
        (∀ x y : SobolevSpaceUp,
          sobolevSpaceToEventFlow x = sobolevSpaceToEventFlow y → x = y) ∧
          sobolevSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨SobolevSpaceTasteGate_single_carrier_alignment_decode,
      SobolevSpaceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => SobolevSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.SobolevSpaceUp
