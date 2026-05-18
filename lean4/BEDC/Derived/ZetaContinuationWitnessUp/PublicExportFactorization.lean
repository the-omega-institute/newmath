import BEDC.Derived.ZetaContinuationWitnessUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_public_export_factorization [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      exportRow hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg ->
      UnaryHistory routes ->
        UnaryHistory name ->
          Cont routes name exportRow ->
            PkgSig bundle exportRow pkg ->
              UnaryHistory exportRow ∧ hsame exportRow (append routes name) ∧
                Cont transports routes provenance ∧ PkgSig bundle name pkg ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle exportRow pkg ∧
                    (Cont exportRow (BHist.e0 hostTail) routes -> False) ∧
                      (Cont exportRow (BHist.e1 hostTail) routes -> False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont hsame UnaryHistory
  intro packet routesUnary nameUnary routesNameExport exportPkg
  obtain ⟨_basicAnalytic, _analyticTransport, _poleGamma, transportsRoutesProvenance,
    namePkg, provenancePkg⟩ := packet
  have exportUnary : UnaryHistory exportRow :=
    unary_cont_closed routesUnary nameUnary routesNameExport
  have e0Refusal : Cont exportRow (BHist.e0 hostTail) routes -> False :=
    fun back => cont_mutual_extension_right_tail_absurd.left routesNameExport back
  have e1Refusal : Cont exportRow (BHist.e1 hostTail) routes -> False :=
    fun back => cont_mutual_extension_right_tail_absurd.right routesNameExport back
  exact
    ⟨exportUnary, routesNameExport, transportsRoutesProvenance, namePkg, provenancePkg,
      exportPkg, e0Refusal, e1Refusal⟩

end BEDC.Derived.ZetaContinuationWitnessUp
