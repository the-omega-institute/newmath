import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformConvergenceSeriesUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformConvergenceSeriesUp : Type where
  | mk (A S W D Q L M E H C P N : BHist) : UniformConvergenceSeriesUp
  deriving DecidableEq

def uniformConvergenceSeriesEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformConvergenceSeriesEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformConvergenceSeriesEncodeBHist h

def uniformConvergenceSeriesDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformConvergenceSeriesDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformConvergenceSeriesDecodeBHist tail)

private theorem UniformConvergenceSeriesTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      uniformConvergenceSeriesDecodeBHist (uniformConvergenceSeriesEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformConvergenceSeriesToEventFlow : UniformConvergenceSeriesUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | UniformConvergenceSeriesUp.mk A S W D Q L M E H C P N =>
      [[BMark.b0],
        uniformConvergenceSeriesEncodeBHist A,
        [BMark.b1, BMark.b0],
        uniformConvergenceSeriesEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b0],
        uniformConvergenceSeriesEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        uniformConvergenceSeriesEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        uniformConvergenceSeriesEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        uniformConvergenceSeriesEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        uniformConvergenceSeriesEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        uniformConvergenceSeriesEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        uniformConvergenceSeriesEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        uniformConvergenceSeriesEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        uniformConvergenceSeriesEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        uniformConvergenceSeriesEncodeBHist N]

private def uniformConvergenceSeriesEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => uniformConvergenceSeriesEventAtDefault index rest

def uniformConvergenceSeriesFromEventFlow
    (ef : EventFlow) : Option UniformConvergenceSeriesUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformConvergenceSeriesUp.mk
      (uniformConvergenceSeriesDecodeBHist (uniformConvergenceSeriesEventAtDefault 1 ef))
      (uniformConvergenceSeriesDecodeBHist (uniformConvergenceSeriesEventAtDefault 3 ef))
      (uniformConvergenceSeriesDecodeBHist (uniformConvergenceSeriesEventAtDefault 5 ef))
      (uniformConvergenceSeriesDecodeBHist (uniformConvergenceSeriesEventAtDefault 7 ef))
      (uniformConvergenceSeriesDecodeBHist (uniformConvergenceSeriesEventAtDefault 9 ef))
      (uniformConvergenceSeriesDecodeBHist (uniformConvergenceSeriesEventAtDefault 11 ef))
      (uniformConvergenceSeriesDecodeBHist (uniformConvergenceSeriesEventAtDefault 13 ef))
      (uniformConvergenceSeriesDecodeBHist (uniformConvergenceSeriesEventAtDefault 15 ef))
      (uniformConvergenceSeriesDecodeBHist (uniformConvergenceSeriesEventAtDefault 17 ef))
      (uniformConvergenceSeriesDecodeBHist (uniformConvergenceSeriesEventAtDefault 19 ef))
      (uniformConvergenceSeriesDecodeBHist (uniformConvergenceSeriesEventAtDefault 21 ef))
      (uniformConvergenceSeriesDecodeBHist (uniformConvergenceSeriesEventAtDefault 23 ef)))

private theorem UniformConvergenceSeriesTasteGate_single_carrier_alignment_round_trip :
    ∀ x : UniformConvergenceSeriesUp,
      uniformConvergenceSeriesFromEventFlow (uniformConvergenceSeriesToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A S W D Q L M E H C P N =>
      change
        some
          (UniformConvergenceSeriesUp.mk
            (uniformConvergenceSeriesDecodeBHist (uniformConvergenceSeriesEncodeBHist A))
            (uniformConvergenceSeriesDecodeBHist (uniformConvergenceSeriesEncodeBHist S))
            (uniformConvergenceSeriesDecodeBHist (uniformConvergenceSeriesEncodeBHist W))
            (uniformConvergenceSeriesDecodeBHist (uniformConvergenceSeriesEncodeBHist D))
            (uniformConvergenceSeriesDecodeBHist (uniformConvergenceSeriesEncodeBHist Q))
            (uniformConvergenceSeriesDecodeBHist (uniformConvergenceSeriesEncodeBHist L))
            (uniformConvergenceSeriesDecodeBHist (uniformConvergenceSeriesEncodeBHist M))
            (uniformConvergenceSeriesDecodeBHist (uniformConvergenceSeriesEncodeBHist E))
            (uniformConvergenceSeriesDecodeBHist (uniformConvergenceSeriesEncodeBHist H))
            (uniformConvergenceSeriesDecodeBHist (uniformConvergenceSeriesEncodeBHist C))
            (uniformConvergenceSeriesDecodeBHist (uniformConvergenceSeriesEncodeBHist P))
            (uniformConvergenceSeriesDecodeBHist (uniformConvergenceSeriesEncodeBHist N))) =
          some (UniformConvergenceSeriesUp.mk A S W D Q L M E H C P N)
      rw [UniformConvergenceSeriesTasteGate_single_carrier_alignment_decode_encode A,
        UniformConvergenceSeriesTasteGate_single_carrier_alignment_decode_encode S,
        UniformConvergenceSeriesTasteGate_single_carrier_alignment_decode_encode W,
        UniformConvergenceSeriesTasteGate_single_carrier_alignment_decode_encode D,
        UniformConvergenceSeriesTasteGate_single_carrier_alignment_decode_encode Q,
        UniformConvergenceSeriesTasteGate_single_carrier_alignment_decode_encode L,
        UniformConvergenceSeriesTasteGate_single_carrier_alignment_decode_encode M,
        UniformConvergenceSeriesTasteGate_single_carrier_alignment_decode_encode E,
        UniformConvergenceSeriesTasteGate_single_carrier_alignment_decode_encode H,
        UniformConvergenceSeriesTasteGate_single_carrier_alignment_decode_encode C,
        UniformConvergenceSeriesTasteGate_single_carrier_alignment_decode_encode P,
        UniformConvergenceSeriesTasteGate_single_carrier_alignment_decode_encode N]

private theorem UniformConvergenceSeriesTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UniformConvergenceSeriesUp} :
    uniformConvergenceSeriesToEventFlow x = uniformConvergenceSeriesToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformConvergenceSeriesFromEventFlow (uniformConvergenceSeriesToEventFlow x) =
        uniformConvergenceSeriesFromEventFlow (uniformConvergenceSeriesToEventFlow y) :=
    congrArg uniformConvergenceSeriesFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (UniformConvergenceSeriesTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (UniformConvergenceSeriesTasteGate_single_carrier_alignment_round_trip y)))

instance uniformConvergenceSeriesBHistCarrier : BHistCarrier UniformConvergenceSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformConvergenceSeriesToEventFlow
  fromEventFlow := uniformConvergenceSeriesFromEventFlow

instance uniformConvergenceSeriesChapterTasteGate :
    ChapterTasteGate UniformConvergenceSeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformConvergenceSeriesFromEventFlow (uniformConvergenceSeriesToEventFlow x) = some x
    exact UniformConvergenceSeriesTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (UniformConvergenceSeriesTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate UniformConvergenceSeriesUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformConvergenceSeriesChapterTasteGate

theorem UniformConvergenceSeriesTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      uniformConvergenceSeriesDecodeBHist (uniformConvergenceSeriesEncodeBHist h) = h) ∧
      (∀ x : UniformConvergenceSeriesUp,
        uniformConvergenceSeriesFromEventFlow (uniformConvergenceSeriesToEventFlow x) =
          some x) ∧
        (∀ x y : UniformConvergenceSeriesUp,
          uniformConvergenceSeriesToEventFlow x = uniformConvergenceSeriesToEventFlow y →
            x = y) ∧
          uniformConvergenceSeriesEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨UniformConvergenceSeriesTasteGate_single_carrier_alignment_decode_encode,
      UniformConvergenceSeriesTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        UniformConvergenceSeriesTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.UniformConvergenceSeriesUp
