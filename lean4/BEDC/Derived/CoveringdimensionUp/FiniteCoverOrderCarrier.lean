import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CoveringDimensionFiniteCoverOrderCarrier [AskSetup] [PackageSetup]
    (compactMetric epsilonNet metricRead regSeqRead realSeal nerve orderTable transport replay
      provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory compactMetric ∧ UnaryHistory epsilonNet ∧ UnaryHistory metricRead ∧
    UnaryHistory regSeqRead ∧ UnaryHistory realSeal ∧ UnaryHistory nerve ∧
      UnaryHistory orderTable ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory localName ∧
          Cont compactMetric epsilonNet metricRead ∧ Cont metricRead regSeqRead realSeal ∧
            Cont epsilonNet nerve orderTable ∧ Cont transport replay provenance ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

end BEDC.Derived.CoveringdimensionUp
