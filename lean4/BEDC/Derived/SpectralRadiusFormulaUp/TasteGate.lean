import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SpectralRadiusFormulaUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SpectralRadiusFormulaUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (A T N P W D R E H C Q L : BHist) : SpectralRadiusFormulaUp
  deriving DecidableEq

def spectralRadiusFormulaEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: spectralRadiusFormulaEncodeBHist h
  | BHist.e1 h => BMark.b1 :: spectralRadiusFormulaEncodeBHist h

def spectralRadiusFormulaDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (spectralRadiusFormulaDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (spectralRadiusFormulaDecodeBHist tail)

private theorem SpectralRadiusFormulaTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, spectralRadiusFormulaDecodeBHist (spectralRadiusFormulaEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def spectralRadiusFormulaFields : SpectralRadiusFormulaUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SpectralRadiusFormulaUp.mk A T N P W D R E H C Q L =>
      [A, T, N, P, W, D, R, E, H, C, Q, L]

def spectralRadiusFormulaToEventFlow : SpectralRadiusFormulaUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (spectralRadiusFormulaFields x).map spectralRadiusFormulaEncodeBHist

private def spectralRadiusFormulaEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => spectralRadiusFormulaEventAt index rest

def spectralRadiusFormulaFromEventFlow (ef : EventFlow) :
    Option SpectralRadiusFormulaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SpectralRadiusFormulaUp.mk
      (spectralRadiusFormulaDecodeBHist (spectralRadiusFormulaEventAt 0 ef))
      (spectralRadiusFormulaDecodeBHist (spectralRadiusFormulaEventAt 1 ef))
      (spectralRadiusFormulaDecodeBHist (spectralRadiusFormulaEventAt 2 ef))
      (spectralRadiusFormulaDecodeBHist (spectralRadiusFormulaEventAt 3 ef))
      (spectralRadiusFormulaDecodeBHist (spectralRadiusFormulaEventAt 4 ef))
      (spectralRadiusFormulaDecodeBHist (spectralRadiusFormulaEventAt 5 ef))
      (spectralRadiusFormulaDecodeBHist (spectralRadiusFormulaEventAt 6 ef))
      (spectralRadiusFormulaDecodeBHist (spectralRadiusFormulaEventAt 7 ef))
      (spectralRadiusFormulaDecodeBHist (spectralRadiusFormulaEventAt 8 ef))
      (spectralRadiusFormulaDecodeBHist (spectralRadiusFormulaEventAt 9 ef))
      (spectralRadiusFormulaDecodeBHist (spectralRadiusFormulaEventAt 10 ef))
      (spectralRadiusFormulaDecodeBHist (spectralRadiusFormulaEventAt 11 ef)))

private theorem SpectralRadiusFormulaTasteGate_single_carrier_alignment_round_trip
    (x : SpectralRadiusFormulaUp) :
    spectralRadiusFormulaFromEventFlow (spectralRadiusFormulaToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk A T N P W D R E H C Q L =>
      change
        some
          (SpectralRadiusFormulaUp.mk
            (spectralRadiusFormulaDecodeBHist (spectralRadiusFormulaEncodeBHist A))
            (spectralRadiusFormulaDecodeBHist (spectralRadiusFormulaEncodeBHist T))
            (spectralRadiusFormulaDecodeBHist (spectralRadiusFormulaEncodeBHist N))
            (spectralRadiusFormulaDecodeBHist (spectralRadiusFormulaEncodeBHist P))
            (spectralRadiusFormulaDecodeBHist (spectralRadiusFormulaEncodeBHist W))
            (spectralRadiusFormulaDecodeBHist (spectralRadiusFormulaEncodeBHist D))
            (spectralRadiusFormulaDecodeBHist (spectralRadiusFormulaEncodeBHist R))
            (spectralRadiusFormulaDecodeBHist (spectralRadiusFormulaEncodeBHist E))
            (spectralRadiusFormulaDecodeBHist (spectralRadiusFormulaEncodeBHist H))
            (spectralRadiusFormulaDecodeBHist (spectralRadiusFormulaEncodeBHist C))
            (spectralRadiusFormulaDecodeBHist (spectralRadiusFormulaEncodeBHist Q))
            (spectralRadiusFormulaDecodeBHist (spectralRadiusFormulaEncodeBHist L))) =
          some (SpectralRadiusFormulaUp.mk A T N P W D R E H C Q L)
      rw [SpectralRadiusFormulaTasteGate_single_carrier_alignment_decode A,
        SpectralRadiusFormulaTasteGate_single_carrier_alignment_decode T,
        SpectralRadiusFormulaTasteGate_single_carrier_alignment_decode N,
        SpectralRadiusFormulaTasteGate_single_carrier_alignment_decode P,
        SpectralRadiusFormulaTasteGate_single_carrier_alignment_decode W,
        SpectralRadiusFormulaTasteGate_single_carrier_alignment_decode D,
        SpectralRadiusFormulaTasteGate_single_carrier_alignment_decode R,
        SpectralRadiusFormulaTasteGate_single_carrier_alignment_decode E,
        SpectralRadiusFormulaTasteGate_single_carrier_alignment_decode H,
        SpectralRadiusFormulaTasteGate_single_carrier_alignment_decode C,
        SpectralRadiusFormulaTasteGate_single_carrier_alignment_decode Q,
        SpectralRadiusFormulaTasteGate_single_carrier_alignment_decode L]

private theorem SpectralRadiusFormulaTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SpectralRadiusFormulaUp} :
    spectralRadiusFormulaToEventFlow x = spectralRadiusFormulaToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      spectralRadiusFormulaFromEventFlow (spectralRadiusFormulaToEventFlow x) =
        spectralRadiusFormulaFromEventFlow (spectralRadiusFormulaToEventFlow y) :=
    congrArg spectralRadiusFormulaFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SpectralRadiusFormulaTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SpectralRadiusFormulaTasteGate_single_carrier_alignment_round_trip y)))

instance spectralRadiusFormulaBHistCarrier : BHistCarrier SpectralRadiusFormulaUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := spectralRadiusFormulaToEventFlow
  fromEventFlow := spectralRadiusFormulaFromEventFlow

instance spectralRadiusFormulaChapterTasteGate :
    ChapterTasteGate SpectralRadiusFormulaUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change spectralRadiusFormulaFromEventFlow (spectralRadiusFormulaToEventFlow x) = some x
    exact SpectralRadiusFormulaTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SpectralRadiusFormulaTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem SpectralRadiusFormulaTasteGate_single_carrier_alignment :
    spectralRadiusFormulaEncodeBHist BHist.Empty = ([] : RawEvent) ∧
      Nonempty (ChapterTasteGate SpectralRadiusFormulaUp) ∧
        ∀ x : SpectralRadiusFormulaUp,
          spectralRadiusFormulaFromEventFlow (spectralRadiusFormulaToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨rfl, ⟨spectralRadiusFormulaChapterTasteGate⟩,
      SpectralRadiusFormulaTasteGate_single_carrier_alignment_round_trip⟩

end BEDC.Derived.SpectralRadiusFormulaUp
