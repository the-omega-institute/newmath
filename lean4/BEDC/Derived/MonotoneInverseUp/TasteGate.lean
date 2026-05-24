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

private theorem MonotoneInverseTasteGate_single_carrier_alignment_injective
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
    exact hxy (MonotoneInverseTasteGate_single_carrier_alignment_injective heq)

theorem MonotoneInverseTasteGate_single_carrier_alignment :
    (∀ h : BHist, monotoneInverseDecodeBHist (monotoneInverseEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier MonotoneInverseUp) ∧
        Nonempty (ChapterTasteGate MonotoneInverseUp) ∧
          monotoneInverseEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact MonotoneInverseTasteGate_single_carrier_alignment_decode
  · constructor
    · exact ⟨monotoneInverseBHistCarrier⟩
    · constructor
      · exact ⟨monotoneInverseChapterTasteGate⟩
      · rfl

end BEDC.Derived.MonotoneInverseUp
