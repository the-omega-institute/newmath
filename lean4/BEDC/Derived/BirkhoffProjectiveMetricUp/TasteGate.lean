import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow

namespace BEDC.Derived.BirkhoffProjectiveMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow

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

end BEDC.Derived.BirkhoffProjectiveMetricUp
