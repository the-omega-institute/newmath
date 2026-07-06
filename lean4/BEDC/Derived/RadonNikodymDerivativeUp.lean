import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RadonNikodymDerivativeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RadonNikodymDerivativePacket [AskSetup] [PackageSetup]
    (baseMeasure acMeasure density window integralReadback nullBoundary transport replay
      provenance localName endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory baseMeasure ∧ UnaryHistory acMeasure ∧ UnaryHistory density ∧
    UnaryHistory window ∧ UnaryHistory integralReadback ∧ UnaryHistory nullBoundary ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ Cont baseMeasure acMeasure density ∧
          Cont density window integralReadback ∧
            Cont integralReadback nullBoundary endpoint ∧ PkgSig bundle endpoint pkg

theorem RadonNikodymDerivativePacket_density_ledger_route [AskSetup] [PackageSetup]
    {baseMeasure acMeasure density window integralReadback nullBoundary transport replay
      provenance localName endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RadonNikodymDerivativePacket baseMeasure acMeasure density window integralReadback
        nullBoundary transport replay provenance localName endpoint bundle pkg ->
      Cont baseMeasure acMeasure density ->
        Cont density window integralReadback ->
          Cont integralReadback nullBoundary endpoint ->
            PkgSig bundle endpoint pkg ->
              UnaryHistory density ∧ UnaryHistory window ∧ UnaryHistory integralReadback ∧
                UnaryHistory nullBoundary ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig
  intro packet baseRoute densityRoute integralRoute endpointPkg
  obtain ⟨baseUnary, acUnary, densityUnary, windowUnary, _integralUnary, nullBoundaryUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, _packetBaseRoute,
    _packetDensityRoute, _packetIntegralRoute, _packetPkg⟩ := packet
  have densityClosed : UnaryHistory density :=
    unary_cont_closed baseUnary acUnary baseRoute
  have integralClosed : UnaryHistory integralReadback :=
    unary_cont_closed densityClosed windowUnary densityRoute
  exact ⟨densityClosed, windowUnary, integralClosed, nullBoundaryUnary, endpointPkg⟩

end BEDC.Derived.RadonNikodymDerivativeUp
