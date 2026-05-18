import BEDC.Derived.ZetaContinuationWitnessUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_zero_route_input_package [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      zeroRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg ->
      UnaryHistory routes ->
        UnaryHistory name ->
          Cont routes name zeroRead ->
            PkgSig bundle zeroRead pkg ->
              UnaryHistory zeroRead ∧ hsame zeroRead (append routes name) ∧
                Cont basic eta analytic ∧ Cont analytic functional transports ∧
                  Cont pole zeroLedger gamma ∧ Cont transports routes provenance ∧
                    PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle zeroRead pkg ∧
                        (Cont zeroRead (BHist.e0 hostTail) routes -> False) ∧
                          (Cont zeroRead (BHist.e1 hostTail) routes -> False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont hsame UnaryHistory
  intro packet routesUnary nameUnary routesNameZero zeroReadPkg
  obtain ⟨basicEtaAnalytic, analyticFunctionalTransports, poleZeroLedgerGamma,
    transportsRoutesProvenance, namePkg, provenancePkg⟩ := packet
  have zeroReadUnary : UnaryHistory zeroRead :=
    unary_cont_closed routesUnary nameUnary routesNameZero
  have e0Refusal : Cont zeroRead (BHist.e0 hostTail) routes -> False :=
    fun hostReturn => cont_mutual_extension_right_tail_absurd.left routesNameZero hostReturn
  have e1Refusal : Cont zeroRead (BHist.e1 hostTail) routes -> False :=
    fun hostReturn => cont_mutual_extension_right_tail_absurd.right routesNameZero hostReturn
  exact
    ⟨zeroReadUnary, routesNameZero, basicEtaAnalytic, analyticFunctionalTransports,
      poleZeroLedgerGamma, transportsRoutesProvenance, namePkg, provenancePkg, zeroReadPkg,
      e0Refusal, e1Refusal⟩

end BEDC.Derived.ZetaContinuationWitnessUp
