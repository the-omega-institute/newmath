import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BrouwerDegreeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BrouwerDegreeUp : Type where
  | mk (K B F O I H T C P N : BHist) : BrouwerDegreeUp
  deriving DecidableEq

def brouwerDegreeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: brouwerDegreeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: brouwerDegreeEncodeBHist h

def brouwerDegreeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (brouwerDegreeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (brouwerDegreeDecodeBHist tail)

private theorem BrouwerDegreeTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, brouwerDegreeDecodeBHist (brouwerDegreeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def brouwerDegreeFields : BrouwerDegreeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BrouwerDegreeUp.mk K B F O I H T C P N => [K, B, F, O, I, H, T, C, P, N]

def brouwerDegreeToEventFlow : BrouwerDegreeUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (brouwerDegreeFields x).map brouwerDegreeEncodeBHist

private def brouwerDegreeEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => brouwerDegreeEventAtDefault index rest

def brouwerDegreeFromEventFlow (ef : EventFlow) : Option BrouwerDegreeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BrouwerDegreeUp.mk
      (brouwerDegreeDecodeBHist (brouwerDegreeEventAtDefault 0 ef))
      (brouwerDegreeDecodeBHist (brouwerDegreeEventAtDefault 1 ef))
      (brouwerDegreeDecodeBHist (brouwerDegreeEventAtDefault 2 ef))
      (brouwerDegreeDecodeBHist (brouwerDegreeEventAtDefault 3 ef))
      (brouwerDegreeDecodeBHist (brouwerDegreeEventAtDefault 4 ef))
      (brouwerDegreeDecodeBHist (brouwerDegreeEventAtDefault 5 ef))
      (brouwerDegreeDecodeBHist (brouwerDegreeEventAtDefault 6 ef))
      (brouwerDegreeDecodeBHist (brouwerDegreeEventAtDefault 7 ef))
      (brouwerDegreeDecodeBHist (brouwerDegreeEventAtDefault 8 ef))
      (brouwerDegreeDecodeBHist (brouwerDegreeEventAtDefault 9 ef)))

private theorem BrouwerDegreeTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BrouwerDegreeUp, brouwerDegreeFromEventFlow (brouwerDegreeToEventFlow x) = some x :=
    by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K B F O I H T C P N =>
      change
        some
          (BrouwerDegreeUp.mk
            (brouwerDegreeDecodeBHist (brouwerDegreeEncodeBHist K))
            (brouwerDegreeDecodeBHist (brouwerDegreeEncodeBHist B))
            (brouwerDegreeDecodeBHist (brouwerDegreeEncodeBHist F))
            (brouwerDegreeDecodeBHist (brouwerDegreeEncodeBHist O))
            (brouwerDegreeDecodeBHist (brouwerDegreeEncodeBHist I))
            (brouwerDegreeDecodeBHist (brouwerDegreeEncodeBHist H))
            (brouwerDegreeDecodeBHist (brouwerDegreeEncodeBHist T))
            (brouwerDegreeDecodeBHist (brouwerDegreeEncodeBHist C))
            (brouwerDegreeDecodeBHist (brouwerDegreeEncodeBHist P))
            (brouwerDegreeDecodeBHist (brouwerDegreeEncodeBHist N))) =
          some (BrouwerDegreeUp.mk K B F O I H T C P N)
      rw [BrouwerDegreeTasteGate_single_carrier_alignment_decode_encode K]
      rw [BrouwerDegreeTasteGate_single_carrier_alignment_decode_encode B]
      rw [BrouwerDegreeTasteGate_single_carrier_alignment_decode_encode F]
      rw [BrouwerDegreeTasteGate_single_carrier_alignment_decode_encode O]
      rw [BrouwerDegreeTasteGate_single_carrier_alignment_decode_encode I]
      rw [BrouwerDegreeTasteGate_single_carrier_alignment_decode_encode H]
      rw [BrouwerDegreeTasteGate_single_carrier_alignment_decode_encode T]
      rw [BrouwerDegreeTasteGate_single_carrier_alignment_decode_encode C]
      rw [BrouwerDegreeTasteGate_single_carrier_alignment_decode_encode P]
      rw [BrouwerDegreeTasteGate_single_carrier_alignment_decode_encode N]

private theorem BrouwerDegreeTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BrouwerDegreeUp} :
    brouwerDegreeToEventFlow x = brouwerDegreeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      brouwerDegreeFromEventFlow (brouwerDegreeToEventFlow x) =
        brouwerDegreeFromEventFlow (brouwerDegreeToEventFlow y) :=
    congrArg brouwerDegreeFromEventFlow heq
  exact
    Option.some.inj
      (Eq.trans
        (BrouwerDegreeTasteGate_single_carrier_alignment_round_trip x).symm
        (Eq.trans hread (BrouwerDegreeTasteGate_single_carrier_alignment_round_trip y)))

private theorem brouwerDegreeFields_faithful :
    ∀ x y : BrouwerDegreeUp, brouwerDegreeFields x = brouwerDegreeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K1 B1 F1 O1 I1 H1 T1 C1 P1 N1 =>
      cases y with
      | mk K2 B2 F2 O2 I2 H2 T2 C2 P2 N2 =>
          cases hfields
          rfl

instance brouwerDegreeBHistCarrier : BHistCarrier BrouwerDegreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := brouwerDegreeToEventFlow
  fromEventFlow := brouwerDegreeFromEventFlow

instance brouwerDegreeChapterTasteGate : ChapterTasteGate BrouwerDegreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change brouwerDegreeFromEventFlow (brouwerDegreeToEventFlow x) = some x
    exact BrouwerDegreeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BrouwerDegreeTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance brouwerDegreeFieldFaithful : FieldFaithful BrouwerDegreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := brouwerDegreeFields
  field_faithful := brouwerDegreeFields_faithful

instance brouwerDegreeNontrivial : BEDC.Meta.TasteGate.Nontrivial BrouwerDegreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BrouwerDegreeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BrouwerDegreeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BrouwerDegreeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  brouwerDegreeChapterTasteGate

theorem BrouwerDegreeTasteGate_single_carrier_alignment :
    ChapterTasteGate BrouwerDegreeUp := by
  -- BEDC touchpoint anchor: BHist BMark
  exact brouwerDegreeChapterTasteGate

end BEDC.Derived.BrouwerDegreeUp
