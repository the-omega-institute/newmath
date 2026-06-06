import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CantorTernarySetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CantorTernarySetUp : Type where
  | mk (W D V G I R E H C P N : BHist) : CantorTernarySetUp
  deriving DecidableEq

def cantorTernarySetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cantorTernarySetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cantorTernarySetEncodeBHist h

def cantorTernarySetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cantorTernarySetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cantorTernarySetDecodeBHist tail)

private theorem CantorTernarySetTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cantorTernarySetDecodeBHist (cantorTernarySetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cantorTernarySetFields : CantorTernarySetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CantorTernarySetUp.mk W D V G I R E H C P N => [W, D, V, G, I, R, E, H, C, P, N]

def cantorTernarySetToEventFlow : CantorTernarySetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cantorTernarySetFields x).map cantorTernarySetEncodeBHist

private def cantorTernarySetEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cantorTernarySetEventAtDefault index rest

def cantorTernarySetFromEventFlow (ef : EventFlow) : Option CantorTernarySetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CantorTernarySetUp.mk
      (cantorTernarySetDecodeBHist (cantorTernarySetEventAtDefault 0 ef))
      (cantorTernarySetDecodeBHist (cantorTernarySetEventAtDefault 1 ef))
      (cantorTernarySetDecodeBHist (cantorTernarySetEventAtDefault 2 ef))
      (cantorTernarySetDecodeBHist (cantorTernarySetEventAtDefault 3 ef))
      (cantorTernarySetDecodeBHist (cantorTernarySetEventAtDefault 4 ef))
      (cantorTernarySetDecodeBHist (cantorTernarySetEventAtDefault 5 ef))
      (cantorTernarySetDecodeBHist (cantorTernarySetEventAtDefault 6 ef))
      (cantorTernarySetDecodeBHist (cantorTernarySetEventAtDefault 7 ef))
      (cantorTernarySetDecodeBHist (cantorTernarySetEventAtDefault 8 ef))
      (cantorTernarySetDecodeBHist (cantorTernarySetEventAtDefault 9 ef))
      (cantorTernarySetDecodeBHist (cantorTernarySetEventAtDefault 10 ef)))

private theorem CantorTernarySetTasteGate_single_carrier_alignment_round_trip
    (x : CantorTernarySetUp) :
    cantorTernarySetFromEventFlow (cantorTernarySetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk W D V G I R E H C P N =>
      change
        some
          (CantorTernarySetUp.mk
            (cantorTernarySetDecodeBHist (cantorTernarySetEncodeBHist W))
            (cantorTernarySetDecodeBHist (cantorTernarySetEncodeBHist D))
            (cantorTernarySetDecodeBHist (cantorTernarySetEncodeBHist V))
            (cantorTernarySetDecodeBHist (cantorTernarySetEncodeBHist G))
            (cantorTernarySetDecodeBHist (cantorTernarySetEncodeBHist I))
            (cantorTernarySetDecodeBHist (cantorTernarySetEncodeBHist R))
            (cantorTernarySetDecodeBHist (cantorTernarySetEncodeBHist E))
            (cantorTernarySetDecodeBHist (cantorTernarySetEncodeBHist H))
            (cantorTernarySetDecodeBHist (cantorTernarySetEncodeBHist C))
            (cantorTernarySetDecodeBHist (cantorTernarySetEncodeBHist P))
            (cantorTernarySetDecodeBHist (cantorTernarySetEncodeBHist N))) =
          some (CantorTernarySetUp.mk W D V G I R E H C P N)
      rw [CantorTernarySetTasteGate_single_carrier_alignment_decode_encode W,
        CantorTernarySetTasteGate_single_carrier_alignment_decode_encode D,
        CantorTernarySetTasteGate_single_carrier_alignment_decode_encode V,
        CantorTernarySetTasteGate_single_carrier_alignment_decode_encode G,
        CantorTernarySetTasteGate_single_carrier_alignment_decode_encode I,
        CantorTernarySetTasteGate_single_carrier_alignment_decode_encode R,
        CantorTernarySetTasteGate_single_carrier_alignment_decode_encode E,
        CantorTernarySetTasteGate_single_carrier_alignment_decode_encode H,
        CantorTernarySetTasteGate_single_carrier_alignment_decode_encode C,
        CantorTernarySetTasteGate_single_carrier_alignment_decode_encode P,
        CantorTernarySetTasteGate_single_carrier_alignment_decode_encode N]

private theorem CantorTernarySetTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CantorTernarySetUp} :
    cantorTernarySetToEventFlow x = cantorTernarySetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cantorTernarySetFromEventFlow (cantorTernarySetToEventFlow x) =
        cantorTernarySetFromEventFlow (cantorTernarySetToEventFlow y) :=
    congrArg cantorTernarySetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CantorTernarySetTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CantorTernarySetTasteGate_single_carrier_alignment_round_trip y)))

instance cantorTernarySetBHistCarrier : BHistCarrier CantorTernarySetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cantorTernarySetToEventFlow
  fromEventFlow := cantorTernarySetFromEventFlow

instance cantorTernarySetChapterTasteGate : ChapterTasteGate CantorTernarySetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cantorTernarySetFromEventFlow (cantorTernarySetToEventFlow x) = some x
    exact CantorTernarySetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CantorTernarySetTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CantorTernarySetTasteGate_single_carrier_alignment {W D V G I R E H C P N : BHist} :
    cantorTernarySetDecodeBHist (cantorTernarySetEncodeBHist BHist.Empty) = BHist.Empty ∧
      (∀ h : BHist, cantorTernarySetDecodeBHist (cantorTernarySetEncodeBHist h) = h) ∧
        cantorTernarySetToEventFlow (CantorTernarySetUp.mk W D V G I R E H C P N) =
          [cantorTernarySetEncodeBHist W, cantorTernarySetEncodeBHist D,
            cantorTernarySetEncodeBHist V, cantorTernarySetEncodeBHist G,
            cantorTernarySetEncodeBHist I, cantorTernarySetEncodeBHist R,
            cantorTernarySetEncodeBHist E, cantorTernarySetEncodeBHist H,
            cantorTernarySetEncodeBHist C, cantorTernarySetEncodeBHist P,
            cantorTernarySetEncodeBHist N] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact ⟨rfl, CantorTernarySetTasteGate_single_carrier_alignment_decode_encode, rfl⟩

end BEDC.Derived.CantorTernarySetUp
