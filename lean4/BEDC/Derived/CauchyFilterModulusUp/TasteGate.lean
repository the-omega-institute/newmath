import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyFilterModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyFilterModulusUp : Type where
  | mk (F B G S D R E H C P N : BHist) : CauchyFilterModulusUp
  deriving DecidableEq

def cauchyFilterModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyFilterModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyFilterModulusEncodeBHist h

def cauchyFilterModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyFilterModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyFilterModulusDecodeBHist tail)

private theorem CauchyFilterModulusTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyFilterModulusDecodeBHist (cauchyFilterModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyFilterModulusFields : CauchyFilterModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyFilterModulusUp.mk F B G S D R E H C P N =>
      [F, B, G, S, D, R, E, H, C, P, N]

def cauchyFilterModulusToEventFlow : CauchyFilterModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map cauchyFilterModulusEncodeBHist (cauchyFilterModulusFields x)

private def cauchyFilterModulusEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyFilterModulusEventAt index rest

def cauchyFilterModulusFromEventFlow : EventFlow → Option CauchyFilterModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (CauchyFilterModulusUp.mk
          (cauchyFilterModulusDecodeBHist (cauchyFilterModulusEventAt 0 ef))
          (cauchyFilterModulusDecodeBHist (cauchyFilterModulusEventAt 1 ef))
          (cauchyFilterModulusDecodeBHist (cauchyFilterModulusEventAt 2 ef))
          (cauchyFilterModulusDecodeBHist (cauchyFilterModulusEventAt 3 ef))
          (cauchyFilterModulusDecodeBHist (cauchyFilterModulusEventAt 4 ef))
          (cauchyFilterModulusDecodeBHist (cauchyFilterModulusEventAt 5 ef))
          (cauchyFilterModulusDecodeBHist (cauchyFilterModulusEventAt 6 ef))
          (cauchyFilterModulusDecodeBHist (cauchyFilterModulusEventAt 7 ef))
          (cauchyFilterModulusDecodeBHist (cauchyFilterModulusEventAt 8 ef))
          (cauchyFilterModulusDecodeBHist (cauchyFilterModulusEventAt 9 ef))
          (cauchyFilterModulusDecodeBHist (cauchyFilterModulusEventAt 10 ef)))

private theorem CauchyFilterModulusTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyFilterModulusUp,
      cauchyFilterModulusFromEventFlow (cauchyFilterModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F B G S D R E H C P N =>
      change
        some
          (CauchyFilterModulusUp.mk
            (cauchyFilterModulusDecodeBHist (cauchyFilterModulusEncodeBHist F))
            (cauchyFilterModulusDecodeBHist (cauchyFilterModulusEncodeBHist B))
            (cauchyFilterModulusDecodeBHist (cauchyFilterModulusEncodeBHist G))
            (cauchyFilterModulusDecodeBHist (cauchyFilterModulusEncodeBHist S))
            (cauchyFilterModulusDecodeBHist (cauchyFilterModulusEncodeBHist D))
            (cauchyFilterModulusDecodeBHist (cauchyFilterModulusEncodeBHist R))
            (cauchyFilterModulusDecodeBHist (cauchyFilterModulusEncodeBHist E))
            (cauchyFilterModulusDecodeBHist (cauchyFilterModulusEncodeBHist H))
            (cauchyFilterModulusDecodeBHist (cauchyFilterModulusEncodeBHist C))
            (cauchyFilterModulusDecodeBHist (cauchyFilterModulusEncodeBHist P))
            (cauchyFilterModulusDecodeBHist (cauchyFilterModulusEncodeBHist N))) =
          some (CauchyFilterModulusUp.mk F B G S D R E H C P N)
      rw [CauchyFilterModulusTasteGate_single_carrier_alignment_decode F,
        CauchyFilterModulusTasteGate_single_carrier_alignment_decode B,
        CauchyFilterModulusTasteGate_single_carrier_alignment_decode G,
        CauchyFilterModulusTasteGate_single_carrier_alignment_decode S,
        CauchyFilterModulusTasteGate_single_carrier_alignment_decode D,
        CauchyFilterModulusTasteGate_single_carrier_alignment_decode R,
        CauchyFilterModulusTasteGate_single_carrier_alignment_decode E,
        CauchyFilterModulusTasteGate_single_carrier_alignment_decode H,
        CauchyFilterModulusTasteGate_single_carrier_alignment_decode C,
        CauchyFilterModulusTasteGate_single_carrier_alignment_decode P,
        CauchyFilterModulusTasteGate_single_carrier_alignment_decode N]

private theorem CauchyFilterModulusTasteGate_single_carrier_alignment_injective
    {x y : CauchyFilterModulusUp} :
    cauchyFilterModulusToEventFlow x = cauchyFilterModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyFilterModulusFromEventFlow (cauchyFilterModulusToEventFlow x) =
        cauchyFilterModulusFromEventFlow (cauchyFilterModulusToEventFlow y) :=
    congrArg cauchyFilterModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyFilterModulusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyFilterModulusTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyFilterModulusBHistCarrier : BHistCarrier CauchyFilterModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyFilterModulusToEventFlow
  fromEventFlow := cauchyFilterModulusFromEventFlow

instance cauchyFilterModulusChapterTasteGate :
    ChapterTasteGate CauchyFilterModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyFilterModulusFromEventFlow (cauchyFilterModulusToEventFlow x) = some x
    exact CauchyFilterModulusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyFilterModulusTasteGate_single_carrier_alignment_injective heq)

theorem CauchyFilterModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyFilterModulusDecodeBHist (cauchyFilterModulusEncodeBHist h) = h) ∧
      (∀ x : CauchyFilterModulusUp,
        cauchyFilterModulusFromEventFlow (cauchyFilterModulusToEventFlow x) = some x) ∧
        (∀ x y : CauchyFilterModulusUp,
          cauchyFilterModulusToEventFlow x = cauchyFilterModulusToEventFlow y ->
            x = y) ∧
          cauchyFilterModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CauchyFilterModulusTasteGate_single_carrier_alignment_decode
  · constructor
    · exact CauchyFilterModulusTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact CauchyFilterModulusTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.CauchyFilterModulusUp
