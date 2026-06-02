import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Unary.History
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CofinalFilterBaseUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CofinalFilterBaseUp : Type where
  | mk (S T rho R F U M H C P N : BHist) : CofinalFilterBaseUp
  deriving DecidableEq

def cofinalFilterBaseEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cofinalFilterBaseEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cofinalFilterBaseEncodeBHist h

def CofinalFilterBaseTasteGate_single_carrier_alignment_decode :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (CofinalFilterBaseTasteGate_single_carrier_alignment_decode tail)
  | BMark.b1 :: tail =>
      BHist.e1 (CofinalFilterBaseTasteGate_single_carrier_alignment_decode tail)

private theorem CofinalFilterBaseTasteGate_single_carrier_alignment_decode_aux :
    ∀ h : BHist,
      CofinalFilterBaseTasteGate_single_carrier_alignment_decode
        (cofinalFilterBaseEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def CofinalFilterBaseTasteGate_single_carrier_alignment_fields :
    CofinalFilterBaseUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CofinalFilterBaseUp.mk S T rho R F U M H C P N => [S, T, rho, R, F, U, M, H, C, P, N]

def CofinalFilterBaseTasteGate_single_carrier_alignment_to_event_flow :
    CofinalFilterBaseUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (CofinalFilterBaseTasteGate_single_carrier_alignment_fields x).map
        cofinalFilterBaseEncodeBHist

private def CofinalFilterBaseTasteGate_single_carrier_alignment_event_at :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      CofinalFilterBaseTasteGate_single_carrier_alignment_event_at index rest

def CofinalFilterBaseTasteGate_single_carrier_alignment_from_event_flow
    (ef : EventFlow) : Option CofinalFilterBaseUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CofinalFilterBaseUp.mk
      (CofinalFilterBaseTasteGate_single_carrier_alignment_decode
        (CofinalFilterBaseTasteGate_single_carrier_alignment_event_at 0 ef))
      (CofinalFilterBaseTasteGate_single_carrier_alignment_decode
        (CofinalFilterBaseTasteGate_single_carrier_alignment_event_at 1 ef))
      (CofinalFilterBaseTasteGate_single_carrier_alignment_decode
        (CofinalFilterBaseTasteGate_single_carrier_alignment_event_at 2 ef))
      (CofinalFilterBaseTasteGate_single_carrier_alignment_decode
        (CofinalFilterBaseTasteGate_single_carrier_alignment_event_at 3 ef))
      (CofinalFilterBaseTasteGate_single_carrier_alignment_decode
        (CofinalFilterBaseTasteGate_single_carrier_alignment_event_at 4 ef))
      (CofinalFilterBaseTasteGate_single_carrier_alignment_decode
        (CofinalFilterBaseTasteGate_single_carrier_alignment_event_at 5 ef))
      (CofinalFilterBaseTasteGate_single_carrier_alignment_decode
        (CofinalFilterBaseTasteGate_single_carrier_alignment_event_at 6 ef))
      (CofinalFilterBaseTasteGate_single_carrier_alignment_decode
        (CofinalFilterBaseTasteGate_single_carrier_alignment_event_at 7 ef))
      (CofinalFilterBaseTasteGate_single_carrier_alignment_decode
        (CofinalFilterBaseTasteGate_single_carrier_alignment_event_at 8 ef))
      (CofinalFilterBaseTasteGate_single_carrier_alignment_decode
        (CofinalFilterBaseTasteGate_single_carrier_alignment_event_at 9 ef))
      (CofinalFilterBaseTasteGate_single_carrier_alignment_decode
        (CofinalFilterBaseTasteGate_single_carrier_alignment_event_at 10 ef)))

private theorem CofinalFilterBaseTasteGate_single_carrier_alignment_round_trip
    (x : CofinalFilterBaseUp) :
    CofinalFilterBaseTasteGate_single_carrier_alignment_from_event_flow
      (CofinalFilterBaseTasteGate_single_carrier_alignment_to_event_flow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S T rho R F U M H C P N =>
      change
        some
          (CofinalFilterBaseUp.mk
            (CofinalFilterBaseTasteGate_single_carrier_alignment_decode
              (cofinalFilterBaseEncodeBHist S))
            (CofinalFilterBaseTasteGate_single_carrier_alignment_decode
              (cofinalFilterBaseEncodeBHist T))
            (CofinalFilterBaseTasteGate_single_carrier_alignment_decode
              (cofinalFilterBaseEncodeBHist rho))
            (CofinalFilterBaseTasteGate_single_carrier_alignment_decode
              (cofinalFilterBaseEncodeBHist R))
            (CofinalFilterBaseTasteGate_single_carrier_alignment_decode
              (cofinalFilterBaseEncodeBHist F))
            (CofinalFilterBaseTasteGate_single_carrier_alignment_decode
              (cofinalFilterBaseEncodeBHist U))
            (CofinalFilterBaseTasteGate_single_carrier_alignment_decode
              (cofinalFilterBaseEncodeBHist M))
            (CofinalFilterBaseTasteGate_single_carrier_alignment_decode
              (cofinalFilterBaseEncodeBHist H))
            (CofinalFilterBaseTasteGate_single_carrier_alignment_decode
              (cofinalFilterBaseEncodeBHist C))
            (CofinalFilterBaseTasteGate_single_carrier_alignment_decode
              (cofinalFilterBaseEncodeBHist P))
            (CofinalFilterBaseTasteGate_single_carrier_alignment_decode
              (cofinalFilterBaseEncodeBHist N))) =
          some (CofinalFilterBaseUp.mk S T rho R F U M H C P N)
      rw [CofinalFilterBaseTasteGate_single_carrier_alignment_decode_aux S,
        CofinalFilterBaseTasteGate_single_carrier_alignment_decode_aux T,
        CofinalFilterBaseTasteGate_single_carrier_alignment_decode_aux rho,
        CofinalFilterBaseTasteGate_single_carrier_alignment_decode_aux R,
        CofinalFilterBaseTasteGate_single_carrier_alignment_decode_aux F,
        CofinalFilterBaseTasteGate_single_carrier_alignment_decode_aux U,
        CofinalFilterBaseTasteGate_single_carrier_alignment_decode_aux M,
        CofinalFilterBaseTasteGate_single_carrier_alignment_decode_aux H,
        CofinalFilterBaseTasteGate_single_carrier_alignment_decode_aux C,
        CofinalFilterBaseTasteGate_single_carrier_alignment_decode_aux P,
        CofinalFilterBaseTasteGate_single_carrier_alignment_decode_aux N]

private theorem CofinalFilterBaseTasteGate_single_carrier_alignment_injective_aux
    {x y : CofinalFilterBaseUp} :
    CofinalFilterBaseTasteGate_single_carrier_alignment_to_event_flow x =
      CofinalFilterBaseTasteGate_single_carrier_alignment_to_event_flow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      CofinalFilterBaseTasteGate_single_carrier_alignment_from_event_flow
          (CofinalFilterBaseTasteGate_single_carrier_alignment_to_event_flow x) =
        CofinalFilterBaseTasteGate_single_carrier_alignment_from_event_flow
          (CofinalFilterBaseTasteGate_single_carrier_alignment_to_event_flow y) :=
    congrArg CofinalFilterBaseTasteGate_single_carrier_alignment_from_event_flow heq
  exact Option.some.inj
    (Eq.trans (CofinalFilterBaseTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CofinalFilterBaseTasteGate_single_carrier_alignment_round_trip y)))

instance CofinalFilterBaseTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier CofinalFilterBaseUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CofinalFilterBaseTasteGate_single_carrier_alignment_to_event_flow
  fromEventFlow := CofinalFilterBaseTasteGate_single_carrier_alignment_from_event_flow

instance CofinalFilterBaseTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate CofinalFilterBaseUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      CofinalFilterBaseTasteGate_single_carrier_alignment_from_event_flow
        (CofinalFilterBaseTasteGate_single_carrier_alignment_to_event_flow x) = some x
    exact CofinalFilterBaseTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CofinalFilterBaseTasteGate_single_carrier_alignment_injective_aux heq)

theorem CofinalFilterBaseTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier CofinalFilterBaseUp) ∧
      Nonempty (ChapterTasteGate CofinalFilterBaseUp) ∧
        cofinalFilterBaseEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨CofinalFilterBaseTasteGate_single_carrier_alignment_BHistCarrier⟩
  · constructor
    · exact ⟨CofinalFilterBaseTasteGate_single_carrier_alignment_ChapterTasteGate⟩
    · rfl

end BEDC.Derived.CofinalFilterBaseUp
