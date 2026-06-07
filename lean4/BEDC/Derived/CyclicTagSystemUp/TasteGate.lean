import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CyclicTagSystemUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CyclicTagSystemUp : Type where
  | mk (A P D W F R H C Q N : BHist) : CyclicTagSystemUp
  deriving DecidableEq

def cyclicTagSystemEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cyclicTagSystemEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cyclicTagSystemEncodeBHist h

def cyclicTagSystemDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cyclicTagSystemDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cyclicTagSystemDecodeBHist tail)

private theorem CyclicTagSystemTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cyclicTagSystemDecodeBHist (cyclicTagSystemEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cyclicTagSystemFields : CyclicTagSystemUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CyclicTagSystemUp.mk A P D W F R H C Q N => [A, P, D, W, F, R, H, C, Q, N]

def cyclicTagSystemToEventFlow : CyclicTagSystemUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cyclicTagSystemFields x).map cyclicTagSystemEncodeBHist

private def cyclicTagSystemEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cyclicTagSystemEventAtDefault index rest

def cyclicTagSystemFromEventFlow (ef : EventFlow) : Option CyclicTagSystemUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CyclicTagSystemUp.mk
      (cyclicTagSystemDecodeBHist (cyclicTagSystemEventAtDefault 0 ef))
      (cyclicTagSystemDecodeBHist (cyclicTagSystemEventAtDefault 1 ef))
      (cyclicTagSystemDecodeBHist (cyclicTagSystemEventAtDefault 2 ef))
      (cyclicTagSystemDecodeBHist (cyclicTagSystemEventAtDefault 3 ef))
      (cyclicTagSystemDecodeBHist (cyclicTagSystemEventAtDefault 4 ef))
      (cyclicTagSystemDecodeBHist (cyclicTagSystemEventAtDefault 5 ef))
      (cyclicTagSystemDecodeBHist (cyclicTagSystemEventAtDefault 6 ef))
      (cyclicTagSystemDecodeBHist (cyclicTagSystemEventAtDefault 7 ef))
      (cyclicTagSystemDecodeBHist (cyclicTagSystemEventAtDefault 8 ef))
      (cyclicTagSystemDecodeBHist (cyclicTagSystemEventAtDefault 9 ef)))

private theorem CyclicTagSystemTasteGate_single_carrier_alignment_round_trip
    (x : CyclicTagSystemUp) :
    cyclicTagSystemFromEventFlow (cyclicTagSystemToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk A P D W F R H C Q N =>
      change
        some
          (CyclicTagSystemUp.mk
            (cyclicTagSystemDecodeBHist (cyclicTagSystemEncodeBHist A))
            (cyclicTagSystemDecodeBHist (cyclicTagSystemEncodeBHist P))
            (cyclicTagSystemDecodeBHist (cyclicTagSystemEncodeBHist D))
            (cyclicTagSystemDecodeBHist (cyclicTagSystemEncodeBHist W))
            (cyclicTagSystemDecodeBHist (cyclicTagSystemEncodeBHist F))
            (cyclicTagSystemDecodeBHist (cyclicTagSystemEncodeBHist R))
            (cyclicTagSystemDecodeBHist (cyclicTagSystemEncodeBHist H))
            (cyclicTagSystemDecodeBHist (cyclicTagSystemEncodeBHist C))
            (cyclicTagSystemDecodeBHist (cyclicTagSystemEncodeBHist Q))
            (cyclicTagSystemDecodeBHist (cyclicTagSystemEncodeBHist N))) =
          some (CyclicTagSystemUp.mk A P D W F R H C Q N)
      rw [CyclicTagSystemTasteGate_single_carrier_alignment_decode_encode A,
        CyclicTagSystemTasteGate_single_carrier_alignment_decode_encode P,
        CyclicTagSystemTasteGate_single_carrier_alignment_decode_encode D,
        CyclicTagSystemTasteGate_single_carrier_alignment_decode_encode W,
        CyclicTagSystemTasteGate_single_carrier_alignment_decode_encode F,
        CyclicTagSystemTasteGate_single_carrier_alignment_decode_encode R,
        CyclicTagSystemTasteGate_single_carrier_alignment_decode_encode H,
        CyclicTagSystemTasteGate_single_carrier_alignment_decode_encode C,
        CyclicTagSystemTasteGate_single_carrier_alignment_decode_encode Q,
        CyclicTagSystemTasteGate_single_carrier_alignment_decode_encode N]

private theorem CyclicTagSystemTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CyclicTagSystemUp} :
    cyclicTagSystemToEventFlow x = cyclicTagSystemToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cyclicTagSystemFromEventFlow (cyclicTagSystemToEventFlow x) =
        cyclicTagSystemFromEventFlow (cyclicTagSystemToEventFlow y) :=
    congrArg cyclicTagSystemFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CyclicTagSystemTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CyclicTagSystemTasteGate_single_carrier_alignment_round_trip y)))

instance cyclicTagSystemBHistCarrier : BHistCarrier CyclicTagSystemUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cyclicTagSystemToEventFlow
  fromEventFlow := cyclicTagSystemFromEventFlow

instance cyclicTagSystemChapterTasteGate : ChapterTasteGate CyclicTagSystemUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cyclicTagSystemFromEventFlow (cyclicTagSystemToEventFlow x) = some x
    exact CyclicTagSystemTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CyclicTagSystemTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CyclicTagSystemTasteGate_single_carrier_alignment {A P D W F R H C Q N : BHist} :
    cyclicTagSystemDecodeBHist (cyclicTagSystemEncodeBHist BHist.Empty) = BHist.Empty ∧
      (∀ h : BHist, cyclicTagSystemDecodeBHist (cyclicTagSystemEncodeBHist h) = h) ∧
        cyclicTagSystemToEventFlow (CyclicTagSystemUp.mk A P D W F R H C Q N) =
          [cyclicTagSystemEncodeBHist A, cyclicTagSystemEncodeBHist P,
            cyclicTagSystemEncodeBHist D, cyclicTagSystemEncodeBHist W,
            cyclicTagSystemEncodeBHist F, cyclicTagSystemEncodeBHist R,
            cyclicTagSystemEncodeBHist H, cyclicTagSystemEncodeBHist C,
            cyclicTagSystemEncodeBHist Q, cyclicTagSystemEncodeBHist N] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact ⟨rfl, CyclicTagSystemTasteGate_single_carrier_alignment_decode_encode, rfl⟩

end BEDC.Derived.CyclicTagSystemUp
