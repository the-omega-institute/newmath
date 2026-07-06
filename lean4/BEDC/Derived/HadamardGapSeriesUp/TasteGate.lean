import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HadamardGapSeriesUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HadamardGapSeriesUp : Type where
  | mk (A G C T R E H K P N : BHist) : HadamardGapSeriesUp
  deriving DecidableEq

def hadamardGapSeriesEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hadamardGapSeriesEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hadamardGapSeriesEncodeBHist h

def hadamardGapSeriesDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hadamardGapSeriesDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hadamardGapSeriesDecodeBHist tail)

private theorem HadamardGapSeriesTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, hadamardGapSeriesDecodeBHist (hadamardGapSeriesEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hadamardGapSeriesFields : HadamardGapSeriesUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HadamardGapSeriesUp.mk A G C T R E H K P N => [A, G, C, T, R, E, H, K, P, N]

def hadamardGapSeriesToEventFlow : HadamardGapSeriesUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (hadamardGapSeriesFields x).map hadamardGapSeriesEncodeBHist

private def hadamardGapSeriesEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hadamardGapSeriesEventAtDefault index rest

def hadamardGapSeriesFromEventFlow (ef : EventFlow) : Option HadamardGapSeriesUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HadamardGapSeriesUp.mk
      (hadamardGapSeriesDecodeBHist (hadamardGapSeriesEventAtDefault 0 ef))
      (hadamardGapSeriesDecodeBHist (hadamardGapSeriesEventAtDefault 1 ef))
      (hadamardGapSeriesDecodeBHist (hadamardGapSeriesEventAtDefault 2 ef))
      (hadamardGapSeriesDecodeBHist (hadamardGapSeriesEventAtDefault 3 ef))
      (hadamardGapSeriesDecodeBHist (hadamardGapSeriesEventAtDefault 4 ef))
      (hadamardGapSeriesDecodeBHist (hadamardGapSeriesEventAtDefault 5 ef))
      (hadamardGapSeriesDecodeBHist (hadamardGapSeriesEventAtDefault 6 ef))
      (hadamardGapSeriesDecodeBHist (hadamardGapSeriesEventAtDefault 7 ef))
      (hadamardGapSeriesDecodeBHist (hadamardGapSeriesEventAtDefault 8 ef))
      (hadamardGapSeriesDecodeBHist (hadamardGapSeriesEventAtDefault 9 ef)))

private theorem HadamardGapSeriesTasteGate_single_carrier_alignment_round_trip :
    ∀ x : HadamardGapSeriesUp,
      hadamardGapSeriesFromEventFlow (hadamardGapSeriesToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A G C T R E H K P N =>
      change
        some
          (HadamardGapSeriesUp.mk
            (hadamardGapSeriesDecodeBHist (hadamardGapSeriesEncodeBHist A))
            (hadamardGapSeriesDecodeBHist (hadamardGapSeriesEncodeBHist G))
            (hadamardGapSeriesDecodeBHist (hadamardGapSeriesEncodeBHist C))
            (hadamardGapSeriesDecodeBHist (hadamardGapSeriesEncodeBHist T))
            (hadamardGapSeriesDecodeBHist (hadamardGapSeriesEncodeBHist R))
            (hadamardGapSeriesDecodeBHist (hadamardGapSeriesEncodeBHist E))
            (hadamardGapSeriesDecodeBHist (hadamardGapSeriesEncodeBHist H))
            (hadamardGapSeriesDecodeBHist (hadamardGapSeriesEncodeBHist K))
            (hadamardGapSeriesDecodeBHist (hadamardGapSeriesEncodeBHist P))
            (hadamardGapSeriesDecodeBHist (hadamardGapSeriesEncodeBHist N))) =
          some (HadamardGapSeriesUp.mk A G C T R E H K P N)
      rw [HadamardGapSeriesTasteGate_single_carrier_alignment_decode A,
        HadamardGapSeriesTasteGate_single_carrier_alignment_decode G,
        HadamardGapSeriesTasteGate_single_carrier_alignment_decode C,
        HadamardGapSeriesTasteGate_single_carrier_alignment_decode T,
        HadamardGapSeriesTasteGate_single_carrier_alignment_decode R,
        HadamardGapSeriesTasteGate_single_carrier_alignment_decode E,
        HadamardGapSeriesTasteGate_single_carrier_alignment_decode H,
        HadamardGapSeriesTasteGate_single_carrier_alignment_decode K,
        HadamardGapSeriesTasteGate_single_carrier_alignment_decode P,
        HadamardGapSeriesTasteGate_single_carrier_alignment_decode N]

private theorem HadamardGapSeriesTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HadamardGapSeriesUp} :
    hadamardGapSeriesToEventFlow x = hadamardGapSeriesToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hadamardGapSeriesFromEventFlow (hadamardGapSeriesToEventFlow x) =
        hadamardGapSeriesFromEventFlow (hadamardGapSeriesToEventFlow y) :=
    congrArg hadamardGapSeriesFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (HadamardGapSeriesTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (HadamardGapSeriesTasteGate_single_carrier_alignment_round_trip y)))

instance hadamardGapSeriesBHistCarrier : BHistCarrier HadamardGapSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hadamardGapSeriesToEventFlow
  fromEventFlow := hadamardGapSeriesFromEventFlow

instance hadamardGapSeriesChapterTasteGate : ChapterTasteGate HadamardGapSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hadamardGapSeriesFromEventFlow (hadamardGapSeriesToEventFlow x) = some x
    exact HadamardGapSeriesTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HadamardGapSeriesTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate HadamardGapSeriesUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hadamardGapSeriesChapterTasteGate

theorem HadamardGapSeriesTasteGate_single_carrier_alignment :
    (forall h : BHist, hadamardGapSeriesDecodeBHist (hadamardGapSeriesEncodeBHist h) = h) ∧
    (forall x : HadamardGapSeriesUp,
      hadamardGapSeriesFromEventFlow (hadamardGapSeriesToEventFlow x) = some x) ∧
    (forall x y : HadamardGapSeriesUp,
      hadamardGapSeriesToEventFlow x = hadamardGapSeriesToEventFlow y -> x = y) ∧
    hadamardGapSeriesEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨HadamardGapSeriesTasteGate_single_carrier_alignment_decode,
      HadamardGapSeriesTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq => HadamardGapSeriesTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.HadamardGapSeriesUp
