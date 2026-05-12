import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.UniformModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def UniformModulusPacket [AskSetup] [PackageSetup]
    (tolerance precision bundleRow radius coverage pointwise foldLedger transport provenance
      nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory tolerance ∧ UnaryHistory precision ∧ UnaryHistory bundleRow ∧
    UnaryHistory radius ∧ UnaryHistory nameRow ∧
      Cont tolerance bundleRow coverage ∧ Cont coverage pointwise transport ∧
        Cont precision radius foldLedger ∧ Cont foldLedger nameRow provenance ∧
          PkgSig bundle provenance pkg

theorem UniformModulusPacket_finite_probe_bundle_fold [AskSetup] [PackageSetup]
    {tolerance precision bundleRow radius coverage pointwise foldLedger transport provenance
      nameRow foldedExport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformModulusPacket tolerance precision bundleRow radius coverage pointwise foldLedger
        transport provenance nameRow bundle pkg ->
      Cont precision radius foldLedger ->
        Cont foldLedger nameRow foldedExport ->
          PkgSig bundle foldedExport pkg ->
            UnaryHistory tolerance ∧ UnaryHistory precision ∧ UnaryHistory bundleRow ∧
              UnaryHistory radius ∧ UnaryHistory foldLedger ∧ UnaryHistory foldedExport ∧
                Cont precision radius foldLedger ∧ Cont foldLedger nameRow foldedExport ∧
                  PkgSig bundle foldedExport pkg := by
  intro packet foldRoute exportRoute exportPkg
  obtain ⟨toleranceUnary, precisionUnary, bundleRowUnary, radiusUnary, nameRowUnary,
    _coverageRoute, _transportRoute, _packetFoldRoute, _provenanceRoute, _provenancePkg⟩ :=
    packet
  have foldUnary : UnaryHistory foldLedger :=
    unary_cont_closed precisionUnary radiusUnary foldRoute
  have exportUnary : UnaryHistory foldedExport :=
    unary_cont_closed foldUnary nameRowUnary exportRoute
  exact
    ⟨toleranceUnary, precisionUnary, bundleRowUnary, radiusUnary, foldUnary, exportUnary,
      foldRoute, exportRoute, exportPkg⟩

end BEDC.Derived.UniformModulusUp
