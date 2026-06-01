import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCutBridgeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCutBridgeUp : Type where
  | mk (Q L D W E H C P N : BHist) : CauchyCutBridgeUp
  deriving DecidableEq

def cauchyCutBridgeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCutBridgeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCutBridgeEncodeBHist h

def cauchyCutBridgeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCutBridgeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCutBridgeDecodeBHist tail)

private theorem CauchyCutBridgeTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, cauchyCutBridgeDecodeBHist (cauchyCutBridgeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCutBridgeFields : CauchyCutBridgeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCutBridgeUp.mk Q L D W E H C P N => [Q, L, D, W, E, H, C, P, N]

def cauchyCutBridgeToEventFlow : CauchyCutBridgeUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cauchyCutBridgeFields x).map cauchyCutBridgeEncodeBHist

private def cauchyCutBridgeEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyCutBridgeEventAtDefault index rest

def cauchyCutBridgeFromEventFlow (ef : EventFlow) : Option CauchyCutBridgeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyCutBridgeUp.mk
      (cauchyCutBridgeDecodeBHist (cauchyCutBridgeEventAtDefault 0 ef))
      (cauchyCutBridgeDecodeBHist (cauchyCutBridgeEventAtDefault 1 ef))
      (cauchyCutBridgeDecodeBHist (cauchyCutBridgeEventAtDefault 2 ef))
      (cauchyCutBridgeDecodeBHist (cauchyCutBridgeEventAtDefault 3 ef))
      (cauchyCutBridgeDecodeBHist (cauchyCutBridgeEventAtDefault 4 ef))
      (cauchyCutBridgeDecodeBHist (cauchyCutBridgeEventAtDefault 5 ef))
      (cauchyCutBridgeDecodeBHist (cauchyCutBridgeEventAtDefault 6 ef))
      (cauchyCutBridgeDecodeBHist (cauchyCutBridgeEventAtDefault 7 ef))
      (cauchyCutBridgeDecodeBHist (cauchyCutBridgeEventAtDefault 8 ef)))

private theorem CauchyCutBridgeTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyCutBridgeUp,
      cauchyCutBridgeFromEventFlow (cauchyCutBridgeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q L D W E H C P N =>
      change
        some
          (CauchyCutBridgeUp.mk
            (cauchyCutBridgeDecodeBHist (cauchyCutBridgeEncodeBHist Q))
            (cauchyCutBridgeDecodeBHist (cauchyCutBridgeEncodeBHist L))
            (cauchyCutBridgeDecodeBHist (cauchyCutBridgeEncodeBHist D))
            (cauchyCutBridgeDecodeBHist (cauchyCutBridgeEncodeBHist W))
            (cauchyCutBridgeDecodeBHist (cauchyCutBridgeEncodeBHist E))
            (cauchyCutBridgeDecodeBHist (cauchyCutBridgeEncodeBHist H))
            (cauchyCutBridgeDecodeBHist (cauchyCutBridgeEncodeBHist C))
            (cauchyCutBridgeDecodeBHist (cauchyCutBridgeEncodeBHist P))
            (cauchyCutBridgeDecodeBHist (cauchyCutBridgeEncodeBHist N))) =
          some (CauchyCutBridgeUp.mk Q L D W E H C P N)
      rw [CauchyCutBridgeTasteGate_single_carrier_alignment_decode Q,
        CauchyCutBridgeTasteGate_single_carrier_alignment_decode L,
        CauchyCutBridgeTasteGate_single_carrier_alignment_decode D,
        CauchyCutBridgeTasteGate_single_carrier_alignment_decode W,
        CauchyCutBridgeTasteGate_single_carrier_alignment_decode E,
        CauchyCutBridgeTasteGate_single_carrier_alignment_decode H,
        CauchyCutBridgeTasteGate_single_carrier_alignment_decode C,
        CauchyCutBridgeTasteGate_single_carrier_alignment_decode P,
        CauchyCutBridgeTasteGate_single_carrier_alignment_decode N]

private theorem CauchyCutBridgeTasteGate_single_carrier_alignment_injective
    {x y : CauchyCutBridgeUp} :
    cauchyCutBridgeToEventFlow x = cauchyCutBridgeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCutBridgeFromEventFlow (cauchyCutBridgeToEventFlow x) =
        cauchyCutBridgeFromEventFlow (cauchyCutBridgeToEventFlow y) :=
    congrArg cauchyCutBridgeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyCutBridgeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyCutBridgeTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyCutBridgeBHistCarrier : BHistCarrier CauchyCutBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCutBridgeToEventFlow
  fromEventFlow := cauchyCutBridgeFromEventFlow

instance cauchyCutBridgeChapterTasteGate : ChapterTasteGate CauchyCutBridgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyCutBridgeFromEventFlow (cauchyCutBridgeToEventFlow x) = some x
    exact CauchyCutBridgeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyCutBridgeTasteGate_single_carrier_alignment_injective heq)

theorem CauchyCutBridgeTasteGate_single_carrier_alignment :
    ChapterTasteGate CauchyCutBridgeUp ∧
      cauchyCutBridgeEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact ⟨cauchyCutBridgeChapterTasteGate, rfl⟩

end BEDC.Derived.CauchyCutBridgeUp
