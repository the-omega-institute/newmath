import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Ext
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FableClockOrderUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Ext
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FableClockOrderCarrier [AskSetup] [PackageSetup]
    (H S T E W L C P N tick witness : BHist) (mark : BMark)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory H ∧ UnaryHistory S ∧ UnaryHistory T ∧ UnaryHistory E ∧ UnaryHistory W ∧
    UnaryHistory L ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
      Ext H mark E ∧ Cont S T tick ∧ Cont E W witness ∧ Cont L C P ∧
        PkgSig bundle N pkg

theorem FableClockOrderCarrier_local_step_order [AskSetup] [PackageSetup]
    {H S T E W L C P N tick witness : BHist} {mark : BMark}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FableClockOrderCarrier H S T E W L C P N tick witness mark bundle pkg ->
      UnaryHistory T ∧ UnaryHistory W ∧ UnaryHistory tick ∧ UnaryHistory witness ∧
        Ext H mark E ∧ Cont S T tick ∧ Cont E W witness ∧ Cont L C P ∧
          PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: FableClockOrderCarrier BHist BMark Ext Cont ProbeBundle Pkg
  intro carrier
  obtain ⟨_HUnary, _SUnary, TUnary, _EUnary, WUnary, _LUnary, _CUnary, _PUnary, _NUnary,
    sourceExt, stepTick, witnessRoute, replayRoute, namePkg⟩ := carrier
  have tickUnary : UnaryHistory tick :=
    unary_cont_closed _SUnary TUnary stepTick
  have witnessUnary : UnaryHistory witness :=
    unary_cont_closed _EUnary WUnary witnessRoute
  exact
    ⟨TUnary, WUnary, tickUnary, witnessUnary, sourceExt, stepTick, witnessRoute,
      replayRoute, namePkg⟩

end BEDC.Derived.FableClockOrderUp
