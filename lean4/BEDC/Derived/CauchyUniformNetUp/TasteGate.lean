import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyUniformNetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyUniformNetUp : Type where
  | mk (I F U W R E H C P N : BHist) : CauchyUniformNetUp
  deriving DecidableEq

def cauchyUniformNetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyUniformNetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyUniformNetEncodeBHist h

def cauchyUniformNetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyUniformNetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyUniformNetDecodeBHist tail)

private theorem CauchyUniformNetTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, cauchyUniformNetDecodeBHist (cauchyUniformNetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyUniformNetToEventFlow : CauchyUniformNetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyUniformNetUp.mk I F U W R E H C P N =>
      [cauchyUniformNetEncodeBHist I,
        cauchyUniformNetEncodeBHist F,
        cauchyUniformNetEncodeBHist U,
        cauchyUniformNetEncodeBHist W,
        cauchyUniformNetEncodeBHist R,
        cauchyUniformNetEncodeBHist E,
        cauchyUniformNetEncodeBHist H,
        cauchyUniformNetEncodeBHist C,
        cauchyUniformNetEncodeBHist P,
        cauchyUniformNetEncodeBHist N]

private def cauchyUniformNetEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyUniformNetEventAtDefault index rest

def cauchyUniformNetFromEventFlow (ef : EventFlow) : Option CauchyUniformNetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyUniformNetUp.mk
      (cauchyUniformNetDecodeBHist (cauchyUniformNetEventAtDefault 0 ef))
      (cauchyUniformNetDecodeBHist (cauchyUniformNetEventAtDefault 1 ef))
      (cauchyUniformNetDecodeBHist (cauchyUniformNetEventAtDefault 2 ef))
      (cauchyUniformNetDecodeBHist (cauchyUniformNetEventAtDefault 3 ef))
      (cauchyUniformNetDecodeBHist (cauchyUniformNetEventAtDefault 4 ef))
      (cauchyUniformNetDecodeBHist (cauchyUniformNetEventAtDefault 5 ef))
      (cauchyUniformNetDecodeBHist (cauchyUniformNetEventAtDefault 6 ef))
      (cauchyUniformNetDecodeBHist (cauchyUniformNetEventAtDefault 7 ef))
      (cauchyUniformNetDecodeBHist (cauchyUniformNetEventAtDefault 8 ef))
      (cauchyUniformNetDecodeBHist (cauchyUniformNetEventAtDefault 9 ef)))

private theorem CauchyUniformNetTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyUniformNetUp,
      cauchyUniformNetFromEventFlow (cauchyUniformNetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I F U W R E H C P N =>
      change
        some
            (CauchyUniformNetUp.mk
              (cauchyUniformNetDecodeBHist (cauchyUniformNetEncodeBHist I))
              (cauchyUniformNetDecodeBHist (cauchyUniformNetEncodeBHist F))
              (cauchyUniformNetDecodeBHist (cauchyUniformNetEncodeBHist U))
              (cauchyUniformNetDecodeBHist (cauchyUniformNetEncodeBHist W))
              (cauchyUniformNetDecodeBHist (cauchyUniformNetEncodeBHist R))
              (cauchyUniformNetDecodeBHist (cauchyUniformNetEncodeBHist E))
              (cauchyUniformNetDecodeBHist (cauchyUniformNetEncodeBHist H))
              (cauchyUniformNetDecodeBHist (cauchyUniformNetEncodeBHist C))
              (cauchyUniformNetDecodeBHist (cauchyUniformNetEncodeBHist P))
              (cauchyUniformNetDecodeBHist (cauchyUniformNetEncodeBHist N))) =
          some (CauchyUniformNetUp.mk I F U W R E H C P N)
      rw [CauchyUniformNetTasteGate_single_carrier_alignment_decode I,
        CauchyUniformNetTasteGate_single_carrier_alignment_decode F,
        CauchyUniformNetTasteGate_single_carrier_alignment_decode U,
        CauchyUniformNetTasteGate_single_carrier_alignment_decode W,
        CauchyUniformNetTasteGate_single_carrier_alignment_decode R,
        CauchyUniformNetTasteGate_single_carrier_alignment_decode E,
        CauchyUniformNetTasteGate_single_carrier_alignment_decode H,
        CauchyUniformNetTasteGate_single_carrier_alignment_decode C,
        CauchyUniformNetTasteGate_single_carrier_alignment_decode P,
        CauchyUniformNetTasteGate_single_carrier_alignment_decode N]

private theorem CauchyUniformNetTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyUniformNetUp} :
    cauchyUniformNetToEventFlow x = cauchyUniformNetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyUniformNetFromEventFlow (cauchyUniformNetToEventFlow x) =
        cauchyUniformNetFromEventFlow (cauchyUniformNetToEventFlow y) :=
    congrArg cauchyUniformNetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyUniformNetTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyUniformNetTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyUniformNetBHistCarrier : BHistCarrier CauchyUniformNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyUniformNetToEventFlow
  fromEventFlow := cauchyUniformNetFromEventFlow

instance cauchyUniformNetChapterTasteGate : ChapterTasteGate CauchyUniformNetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyUniformNetFromEventFlow (cauchyUniformNetToEventFlow x) = some x
    exact CauchyUniformNetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyUniformNetTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyUniformNetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyUniformNetChapterTasteGate

theorem CauchyUniformNetTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyUniformNetDecodeBHist (cauchyUniformNetEncodeBHist h) = h) ∧
      (∀ x : CauchyUniformNetUp,
        cauchyUniformNetFromEventFlow (cauchyUniformNetToEventFlow x) = some x) ∧
        (∀ x y : CauchyUniformNetUp,
          cauchyUniformNetToEventFlow x = cauchyUniformNetToEventFlow y → x = y) ∧
          cauchyUniformNetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CauchyUniformNetTasteGate_single_carrier_alignment_decode,
      CauchyUniformNetTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => CauchyUniformNetTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyUniformNetUp
