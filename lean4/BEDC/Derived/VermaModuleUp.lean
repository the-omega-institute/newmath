import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.VermaModuleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem VermaModuleHighestWeightLedger_boundary [AskSetup] [PackageSetup]
    {lie roots highest borel generator provenance endpoint lowering readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory lie -> UnaryHistory roots -> UnaryHistory highest -> UnaryHistory lowering ->
      Cont lie roots highest -> Cont highest borel generator ->
        Cont generator provenance endpoint -> Cont highest lowering readback ->
          Cont readback provenance endpoint -> PkgSig bundle endpoint pkg ->
            UnaryHistory readback ∧ Cont highest lowering readback ∧
              Cont readback provenance endpoint ∧ PkgSig bundle endpoint pkg := by
  intro _lieUnary _rootsUnary highestUnary loweringUnary _lieRootsRow _borelRow
    _generatorEndpointRow loweringRow readbackEndpointRow pkgSig
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed highestUnary loweringUnary loweringRow
  exact And.intro readbackUnary
    (And.intro loweringRow (And.intro readbackEndpointRow pkgSig))

end BEDC.Derived.VermaModuleUp
