import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MonotoneInverseUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MonotoneInverseUp : Type where
  | mk (A T M B W R D E H C P N : BHist) : MonotoneInverseUp
  deriving DecidableEq

def monotoneInverseEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: monotoneInverseEncodeBHist h
  | BHist.e1 h => BMark.b1 :: monotoneInverseEncodeBHist h

def monotoneInverseDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (monotoneInverseDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (monotoneInverseDecodeBHist tail)

private theorem MonotoneInverseTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, monotoneInverseDecodeBHist (monotoneInverseEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def monotoneInverseFields : MonotoneInverseUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MonotoneInverseUp.mk A T M B W R D E H C P N => [A, T, M, B, W, R, D, E, H, C, P, N]

def monotoneInverseToEventFlow : MonotoneInverseUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (monotoneInverseFields x).map monotoneInverseEncodeBHist

private def monotoneInverseEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => monotoneInverseEventAtDefault index rest

def monotoneInverseFromEventFlow (ef : EventFlow) : Option MonotoneInverseUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MonotoneInverseUp.mk
      (monotoneInverseDecodeBHist (monotoneInverseEventAtDefault 0 ef))
      (monotoneInverseDecodeBHist (monotoneInverseEventAtDefault 1 ef))
      (monotoneInverseDecodeBHist (monotoneInverseEventAtDefault 2 ef))
      (monotoneInverseDecodeBHist (monotoneInverseEventAtDefault 3 ef))
      (monotoneInverseDecodeBHist (monotoneInverseEventAtDefault 4 ef))
      (monotoneInverseDecodeBHist (monotoneInverseEventAtDefault 5 ef))
      (monotoneInverseDecodeBHist (monotoneInverseEventAtDefault 6 ef))
      (monotoneInverseDecodeBHist (monotoneInverseEventAtDefault 7 ef))
      (monotoneInverseDecodeBHist (monotoneInverseEventAtDefault 8 ef))
      (monotoneInverseDecodeBHist (monotoneInverseEventAtDefault 9 ef))
      (monotoneInverseDecodeBHist (monotoneInverseEventAtDefault 10 ef))
      (monotoneInverseDecodeBHist (monotoneInverseEventAtDefault 11 ef)))

private theorem MonotoneInverseTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MonotoneInverseUp,
      monotoneInverseFromEventFlow (monotoneInverseToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A T M B W R D E H C P N =>
      change
        some
          (MonotoneInverseUp.mk
            (monotoneInverseDecodeBHist (monotoneInverseEncodeBHist A))
            (monotoneInverseDecodeBHist (monotoneInverseEncodeBHist T))
            (monotoneInverseDecodeBHist (monotoneInverseEncodeBHist M))
            (monotoneInverseDecodeBHist (monotoneInverseEncodeBHist B))
            (monotoneInverseDecodeBHist (monotoneInverseEncodeBHist W))
            (monotoneInverseDecodeBHist (monotoneInverseEncodeBHist R))
            (monotoneInverseDecodeBHist (monotoneInverseEncodeBHist D))
            (monotoneInverseDecodeBHist (monotoneInverseEncodeBHist E))
            (monotoneInverseDecodeBHist (monotoneInverseEncodeBHist H))
            (monotoneInverseDecodeBHist (monotoneInverseEncodeBHist C))
            (monotoneInverseDecodeBHist (monotoneInverseEncodeBHist P))
            (monotoneInverseDecodeBHist (monotoneInverseEncodeBHist N))) =
          some (MonotoneInverseUp.mk A T M B W R D E H C P N)
      rw [MonotoneInverseTasteGate_single_carrier_alignment_decode A,
        MonotoneInverseTasteGate_single_carrier_alignment_decode T,
        MonotoneInverseTasteGate_single_carrier_alignment_decode M,
        MonotoneInverseTasteGate_single_carrier_alignment_decode B,
        MonotoneInverseTasteGate_single_carrier_alignment_decode W,
        MonotoneInverseTasteGate_single_carrier_alignment_decode R,
        MonotoneInverseTasteGate_single_carrier_alignment_decode D,
        MonotoneInverseTasteGate_single_carrier_alignment_decode E,
        MonotoneInverseTasteGate_single_carrier_alignment_decode H,
        MonotoneInverseTasteGate_single_carrier_alignment_decode C,
        MonotoneInverseTasteGate_single_carrier_alignment_decode P,
        MonotoneInverseTasteGate_single_carrier_alignment_decode N]

private theorem MonotoneInverseTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MonotoneInverseUp} :
    monotoneInverseToEventFlow x = monotoneInverseToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      monotoneInverseFromEventFlow (monotoneInverseToEventFlow x) =
        monotoneInverseFromEventFlow (monotoneInverseToEventFlow y) :=
    congrArg monotoneInverseFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MonotoneInverseTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MonotoneInverseTasteGate_single_carrier_alignment_round_trip y)))

private theorem MonotoneInverseTasteGate_single_carrier_alignment_fields :
    ∀ x y : MonotoneInverseUp, monotoneInverseFields x = monotoneInverseFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A1 T1 M1 B1 W1 R1 D1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk A2 T2 M2 B2 W2 R2 D2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance monotoneInverseBHistCarrier : BHistCarrier MonotoneInverseUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := monotoneInverseToEventFlow
  fromEventFlow := monotoneInverseFromEventFlow

instance monotoneInverseChapterTasteGate : ChapterTasteGate MonotoneInverseUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change monotoneInverseFromEventFlow (monotoneInverseToEventFlow x) = some x
    exact MonotoneInverseTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MonotoneInverseTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance monotoneInverseFieldFaithful : FieldFaithful MonotoneInverseUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := monotoneInverseFields
  field_faithful := MonotoneInverseTasteGate_single_carrier_alignment_fields

instance monotoneInverseNontrivial : BEDC.Meta.TasteGate.Nontrivial MonotoneInverseUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MonotoneInverseUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MonotoneInverseUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MonotoneInverseUp :=
  -- BEDC touchpoint anchor: BHist BMark
  monotoneInverseChapterTasteGate

theorem MonotoneInverseTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate MonotoneInverseUp) ∧
      Nonempty (FieldFaithful MonotoneInverseUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial MonotoneInverseUp) ∧
          (∀ h : BHist, monotoneInverseDecodeBHist (monotoneInverseEncodeBHist h) = h) ∧
            (∀ x : MonotoneInverseUp,
              monotoneInverseFromEventFlow (monotoneInverseToEventFlow x) = some x) ∧
              (∀ x y : MonotoneInverseUp,
                monotoneInverseToEventFlow x = monotoneInverseToEventFlow y → x = y) ∧
                monotoneInverseEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨monotoneInverseChapterTasteGate⟩,
      ⟨monotoneInverseFieldFaithful⟩,
      ⟨monotoneInverseNontrivial⟩,
      MonotoneInverseTasteGate_single_carrier_alignment_decode,
      MonotoneInverseTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        MonotoneInverseTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.MonotoneInverseUp
