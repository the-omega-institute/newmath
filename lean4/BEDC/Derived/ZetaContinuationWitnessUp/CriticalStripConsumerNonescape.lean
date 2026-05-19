import BEDC.Derived.ZetaContinuationWitnessUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_critical_strip_consumer_nonescape
    [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      criticalRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg ->
      UnaryHistory routes ->
        UnaryHistory name ->
          Cont routes name criticalRead ->
            PkgSig bundle criticalRead pkg ->
              UnaryHistory criticalRead ∧ hsame criticalRead (append routes name) ∧
                Cont transports routes provenance ∧ PkgSig bundle name pkg ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle criticalRead pkg ∧
                    (Cont criticalRead (BHist.e0 hostTail) routes -> False) ∧
                      (Cont criticalRead (BHist.e1 hostTail) routes -> False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont hsame UnaryHistory
  intro packet routesUnary nameUnary routesNameCritical criticalPkg
  have projected :=
    ZetaContinuationWitnessPacket_critical_strip_input_refusal
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (zeroLedger := zeroLedger) (gamma := gamma)
      (transports := transports) (routes := routes) (provenance := provenance)
      (name := name) (criticalRead := criticalRead) (bundle := bundle) (pkg := pkg)
      packet routesUnary nameUnary routesNameCritical
  obtain ⟨criticalUnary, sameCritical, transportsRoutesProvenance, namePkg,
    provenancePkg⟩ := projected
  have e0Refusal : Cont criticalRead (BHist.e0 hostTail) routes -> False :=
    fun hostReturn => cont_mutual_extension_right_tail_absurd.left routesNameCritical hostReturn
  have e1Refusal : Cont criticalRead (BHist.e1 hostTail) routes -> False :=
    fun hostReturn => cont_mutual_extension_right_tail_absurd.right routesNameCritical hostReturn
  exact
    ⟨criticalUnary, sameCritical, transportsRoutesProvenance, namePkg, provenancePkg,
      criticalPkg, e0Refusal, e1Refusal⟩

end BEDC.Derived.ZetaContinuationWitnessUp
