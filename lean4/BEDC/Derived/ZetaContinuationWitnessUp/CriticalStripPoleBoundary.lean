import BEDC.Derived.ZetaContinuationWitnessUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessCriticalStripPoleBoundary [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      criticalRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg ->
      UnaryHistory routes ->
        UnaryHistory name ->
          Cont routes name criticalRead ->
            PkgSig bundle criticalRead pkg ->
              UnaryHistory criticalRead /\ hsame criticalRead (append routes name) /\
                Cont pole zeroLedger gamma /\ Cont analytic functional transports /\
                  PkgSig bundle name pkg /\ PkgSig bundle provenance pkg /\
                    PkgSig bundle criticalRead pkg /\
                      (Cont criticalRead (BHist.e0 hostTail) routes -> False) /\
                        (Cont criticalRead (BHist.e1 hostTail) routes -> False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet routesUnary nameUnary routesNameCritical criticalReadPkg
  obtain ⟨_basicEtaAnalytic, analyticFunctionalTransports, poleZeroLedgerGamma,
    _transportsRoutesProvenance, namePkg, provenancePkg⟩ := packet
  have criticalUnary : UnaryHistory criticalRead :=
    unary_cont_closed routesUnary nameUnary routesNameCritical
  have noZeroTail : Cont criticalRead (BHist.e0 hostTail) routes -> False := by
    intro criticalZeroRoutes
    have cycle : Cont routes (BHist.e0 (append name hostTail)) routes := by
      cases routesNameCritical
      exact criticalZeroRoutes.trans (append_assoc routes name (BHist.e0 hostTail))
    exact (cont_self_extension_tail_absurd (h := routes) (tail := append name hostTail)).left cycle
  have noOneTail : Cont criticalRead (BHist.e1 hostTail) routes -> False := by
    intro criticalOneRoutes
    have cycle : Cont routes (BHist.e1 (append name hostTail)) routes := by
      cases routesNameCritical
      exact criticalOneRoutes.trans (append_assoc routes name (BHist.e1 hostTail))
    exact (cont_self_extension_tail_absurd (h := routes) (tail := append name hostTail)).right cycle
  exact
    ⟨criticalUnary, routesNameCritical, poleZeroLedgerGamma, analyticFunctionalTransports,
      namePkg, provenancePkg, criticalReadPkg, noZeroTail, noOneTail⟩

end BEDC.Derived.ZetaContinuationWitnessUp
