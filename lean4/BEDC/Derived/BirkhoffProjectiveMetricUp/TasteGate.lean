import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BirkhoffProjectiveMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BirkhoffProjectiveMetricUp : Type where
  | mk (K x y U L rho d M G H C P N : BHist) : BirkhoffProjectiveMetricUp
  deriving DecidableEq

def birkhoffProjectiveMetricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: birkhoffProjectiveMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: birkhoffProjectiveMetricEncodeBHist h

def birkhoffProjectiveMetricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (birkhoffProjectiveMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (birkhoffProjectiveMetricDecodeBHist tail)

private theorem BirkhoffProjectiveMetricTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      birkhoffProjectiveMetricDecodeBHist (birkhoffProjectiveMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def birkhoffProjectiveMetricToEventFlow : BirkhoffProjectiveMetricUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BirkhoffProjectiveMetricUp.mk K x y U L rho d M G H C P N =>
      [birkhoffProjectiveMetricEncodeBHist K,
        birkhoffProjectiveMetricEncodeBHist x,
        birkhoffProjectiveMetricEncodeBHist y,
        birkhoffProjectiveMetricEncodeBHist U,
        birkhoffProjectiveMetricEncodeBHist L,
        birkhoffProjectiveMetricEncodeBHist rho,
        birkhoffProjectiveMetricEncodeBHist d,
        birkhoffProjectiveMetricEncodeBHist M,
        birkhoffProjectiveMetricEncodeBHist G,
        birkhoffProjectiveMetricEncodeBHist H,
        birkhoffProjectiveMetricEncodeBHist C,
        birkhoffProjectiveMetricEncodeBHist P,
        birkhoffProjectiveMetricEncodeBHist N]

def birkhoffProjectiveMetricFromEventFlow : EventFlow → Option BirkhoffProjectiveMetricUp
  -- BEDC touchpoint anchor: BHist BMark
  | K :: x :: y :: U :: L :: rho :: d :: M :: G :: H :: C :: P :: N :: [] =>
      some
        (BirkhoffProjectiveMetricUp.mk
          (birkhoffProjectiveMetricDecodeBHist K)
          (birkhoffProjectiveMetricDecodeBHist x)
          (birkhoffProjectiveMetricDecodeBHist y)
          (birkhoffProjectiveMetricDecodeBHist U)
          (birkhoffProjectiveMetricDecodeBHist L)
          (birkhoffProjectiveMetricDecodeBHist rho)
          (birkhoffProjectiveMetricDecodeBHist d)
          (birkhoffProjectiveMetricDecodeBHist M)
          (birkhoffProjectiveMetricDecodeBHist G)
          (birkhoffProjectiveMetricDecodeBHist H)
          (birkhoffProjectiveMetricDecodeBHist C)
          (birkhoffProjectiveMetricDecodeBHist P)
          (birkhoffProjectiveMetricDecodeBHist N))
  | _ => none

private theorem BirkhoffProjectiveMetricTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BirkhoffProjectiveMetricUp,
      birkhoffProjectiveMetricFromEventFlow (birkhoffProjectiveMetricToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk K x y U L rho d M G H C P N =>
      change
        some
          (BirkhoffProjectiveMetricUp.mk
            (birkhoffProjectiveMetricDecodeBHist (birkhoffProjectiveMetricEncodeBHist K))
            (birkhoffProjectiveMetricDecodeBHist (birkhoffProjectiveMetricEncodeBHist x))
            (birkhoffProjectiveMetricDecodeBHist (birkhoffProjectiveMetricEncodeBHist y))
            (birkhoffProjectiveMetricDecodeBHist (birkhoffProjectiveMetricEncodeBHist U))
            (birkhoffProjectiveMetricDecodeBHist (birkhoffProjectiveMetricEncodeBHist L))
            (birkhoffProjectiveMetricDecodeBHist (birkhoffProjectiveMetricEncodeBHist rho))
            (birkhoffProjectiveMetricDecodeBHist (birkhoffProjectiveMetricEncodeBHist d))
            (birkhoffProjectiveMetricDecodeBHist (birkhoffProjectiveMetricEncodeBHist M))
            (birkhoffProjectiveMetricDecodeBHist (birkhoffProjectiveMetricEncodeBHist G))
            (birkhoffProjectiveMetricDecodeBHist (birkhoffProjectiveMetricEncodeBHist H))
            (birkhoffProjectiveMetricDecodeBHist (birkhoffProjectiveMetricEncodeBHist C))
            (birkhoffProjectiveMetricDecodeBHist (birkhoffProjectiveMetricEncodeBHist P))
            (birkhoffProjectiveMetricDecodeBHist (birkhoffProjectiveMetricEncodeBHist N))) =
          some (BirkhoffProjectiveMetricUp.mk K x y U L rho d M G H C P N)
      rw [BirkhoffProjectiveMetricTasteGate_single_carrier_alignment_decode K,
        BirkhoffProjectiveMetricTasteGate_single_carrier_alignment_decode x,
        BirkhoffProjectiveMetricTasteGate_single_carrier_alignment_decode y,
        BirkhoffProjectiveMetricTasteGate_single_carrier_alignment_decode U,
        BirkhoffProjectiveMetricTasteGate_single_carrier_alignment_decode L,
        BirkhoffProjectiveMetricTasteGate_single_carrier_alignment_decode rho,
        BirkhoffProjectiveMetricTasteGate_single_carrier_alignment_decode d,
        BirkhoffProjectiveMetricTasteGate_single_carrier_alignment_decode M,
        BirkhoffProjectiveMetricTasteGate_single_carrier_alignment_decode G,
        BirkhoffProjectiveMetricTasteGate_single_carrier_alignment_decode H,
        BirkhoffProjectiveMetricTasteGate_single_carrier_alignment_decode C,
        BirkhoffProjectiveMetricTasteGate_single_carrier_alignment_decode P,
        BirkhoffProjectiveMetricTasteGate_single_carrier_alignment_decode N]

private theorem BirkhoffProjectiveMetricTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BirkhoffProjectiveMetricUp} :
    birkhoffProjectiveMetricToEventFlow x = birkhoffProjectiveMetricToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      birkhoffProjectiveMetricFromEventFlow (birkhoffProjectiveMetricToEventFlow x) =
        birkhoffProjectiveMetricFromEventFlow (birkhoffProjectiveMetricToEventFlow y) :=
    congrArg birkhoffProjectiveMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BirkhoffProjectiveMetricTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BirkhoffProjectiveMetricTasteGate_single_carrier_alignment_round_trip y)))

instance birkhoffProjectiveMetricBHistCarrier : BHistCarrier BirkhoffProjectiveMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := birkhoffProjectiveMetricToEventFlow
  fromEventFlow := birkhoffProjectiveMetricFromEventFlow

instance birkhoffProjectiveMetricChapterTasteGate :
    ChapterTasteGate BirkhoffProjectiveMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      birkhoffProjectiveMetricFromEventFlow (birkhoffProjectiveMetricToEventFlow x) = some x
    exact BirkhoffProjectiveMetricTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BirkhoffProjectiveMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate BirkhoffProjectiveMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  birkhoffProjectiveMetricChapterTasteGate

theorem BirkhoffProjectiveMetricTasteGate_single_carrier_alignment :
    (∀ h : BHist, birkhoffProjectiveMetricDecodeBHist
        (birkhoffProjectiveMetricEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BirkhoffProjectiveMetricUp) ∧
        Nonempty (ChapterTasteGate BirkhoffProjectiveMetricUp) ∧
          birkhoffProjectiveMetricEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨BirkhoffProjectiveMetricTasteGate_single_carrier_alignment_decode,
      ⟨birkhoffProjectiveMetricBHistCarrier⟩,
      ⟨birkhoffProjectiveMetricChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.BirkhoffProjectiveMetricUp
