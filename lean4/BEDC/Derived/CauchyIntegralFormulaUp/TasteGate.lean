import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyIntegralFormulaUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyIntegralFormulaUp : Type where
  | mk (D Z R H C S G L T P N : BHist) : CauchyIntegralFormulaUp
  deriving DecidableEq

def cauchyIntegralFormulaEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyIntegralFormulaEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyIntegralFormulaEncodeBHist h

def cauchyIntegralFormulaDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyIntegralFormulaDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyIntegralFormulaDecodeBHist tail)

private theorem CauchyIntegralFormulaTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyIntegralFormulaDecodeBHist (cauchyIntegralFormulaEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyIntegralFormulaFields : CauchyIntegralFormulaUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyIntegralFormulaUp.mk D Z R H C S G L T P N =>
      [D, Z, R, H, C, S, G, L, T, P, N]

def cauchyIntegralFormulaToEventFlow : CauchyIntegralFormulaUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyIntegralFormulaFields x).map cauchyIntegralFormulaEncodeBHist

private def cauchyIntegralFormulaEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyIntegralFormulaEventAt index rest

def cauchyIntegralFormulaFromEventFlow
    (ef : EventFlow) : Option CauchyIntegralFormulaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyIntegralFormulaUp.mk
      (cauchyIntegralFormulaDecodeBHist (cauchyIntegralFormulaEventAt 0 ef))
      (cauchyIntegralFormulaDecodeBHist (cauchyIntegralFormulaEventAt 1 ef))
      (cauchyIntegralFormulaDecodeBHist (cauchyIntegralFormulaEventAt 2 ef))
      (cauchyIntegralFormulaDecodeBHist (cauchyIntegralFormulaEventAt 3 ef))
      (cauchyIntegralFormulaDecodeBHist (cauchyIntegralFormulaEventAt 4 ef))
      (cauchyIntegralFormulaDecodeBHist (cauchyIntegralFormulaEventAt 5 ef))
      (cauchyIntegralFormulaDecodeBHist (cauchyIntegralFormulaEventAt 6 ef))
      (cauchyIntegralFormulaDecodeBHist (cauchyIntegralFormulaEventAt 7 ef))
      (cauchyIntegralFormulaDecodeBHist (cauchyIntegralFormulaEventAt 8 ef))
      (cauchyIntegralFormulaDecodeBHist (cauchyIntegralFormulaEventAt 9 ef))
      (cauchyIntegralFormulaDecodeBHist (cauchyIntegralFormulaEventAt 10 ef)))

private theorem CauchyIntegralFormulaTasteGate_single_carrier_alignment_round_trip
    (x : CauchyIntegralFormulaUp) :
    cauchyIntegralFormulaFromEventFlow
        (cauchyIntegralFormulaToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D Z R H C S G L T P N =>
      change
        some
            (CauchyIntegralFormulaUp.mk
              (cauchyIntegralFormulaDecodeBHist (cauchyIntegralFormulaEncodeBHist D))
              (cauchyIntegralFormulaDecodeBHist (cauchyIntegralFormulaEncodeBHist Z))
              (cauchyIntegralFormulaDecodeBHist (cauchyIntegralFormulaEncodeBHist R))
              (cauchyIntegralFormulaDecodeBHist (cauchyIntegralFormulaEncodeBHist H))
              (cauchyIntegralFormulaDecodeBHist (cauchyIntegralFormulaEncodeBHist C))
              (cauchyIntegralFormulaDecodeBHist (cauchyIntegralFormulaEncodeBHist S))
              (cauchyIntegralFormulaDecodeBHist (cauchyIntegralFormulaEncodeBHist G))
              (cauchyIntegralFormulaDecodeBHist (cauchyIntegralFormulaEncodeBHist L))
              (cauchyIntegralFormulaDecodeBHist (cauchyIntegralFormulaEncodeBHist T))
              (cauchyIntegralFormulaDecodeBHist (cauchyIntegralFormulaEncodeBHist P))
              (cauchyIntegralFormulaDecodeBHist (cauchyIntegralFormulaEncodeBHist N))) =
          some (CauchyIntegralFormulaUp.mk D Z R H C S G L T P N)
      rw [CauchyIntegralFormulaTasteGate_single_carrier_alignment_decode_encode D,
        CauchyIntegralFormulaTasteGate_single_carrier_alignment_decode_encode Z,
        CauchyIntegralFormulaTasteGate_single_carrier_alignment_decode_encode R,
        CauchyIntegralFormulaTasteGate_single_carrier_alignment_decode_encode H,
        CauchyIntegralFormulaTasteGate_single_carrier_alignment_decode_encode C,
        CauchyIntegralFormulaTasteGate_single_carrier_alignment_decode_encode S,
        CauchyIntegralFormulaTasteGate_single_carrier_alignment_decode_encode G,
        CauchyIntegralFormulaTasteGate_single_carrier_alignment_decode_encode L,
        CauchyIntegralFormulaTasteGate_single_carrier_alignment_decode_encode T,
        CauchyIntegralFormulaTasteGate_single_carrier_alignment_decode_encode P,
        CauchyIntegralFormulaTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyIntegralFormulaTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyIntegralFormulaUp} :
    cauchyIntegralFormulaToEventFlow x = cauchyIntegralFormulaToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyIntegralFormulaFromEventFlow (cauchyIntegralFormulaToEventFlow x) =
        cauchyIntegralFormulaFromEventFlow (cauchyIntegralFormulaToEventFlow y) :=
    congrArg cauchyIntegralFormulaFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyIntegralFormulaTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyIntegralFormulaTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyIntegralFormulaBHistCarrier : BHistCarrier CauchyIntegralFormulaUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyIntegralFormulaToEventFlow
  fromEventFlow := cauchyIntegralFormulaFromEventFlow

instance cauchyIntegralFormulaChapterTasteGate : ChapterTasteGate CauchyIntegralFormulaUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyIntegralFormulaFromEventFlow (cauchyIntegralFormulaToEventFlow x) = some x
    exact CauchyIntegralFormulaTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyIntegralFormulaTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyIntegralFormulaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyIntegralFormulaChapterTasteGate

theorem CauchyIntegralFormulaTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyIntegralFormulaDecodeBHist
      (cauchyIntegralFormulaEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CauchyIntegralFormulaUp) ∧
        Nonempty (ChapterTasteGate CauchyIntegralFormulaUp) ∧
          cauchyIntegralFormulaEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyIntegralFormulaTasteGate_single_carrier_alignment_decode_encode,
      ⟨cauchyIntegralFormulaBHistCarrier⟩,
      ⟨cauchyIntegralFormulaChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CauchyIntegralFormulaUp
