import BEDC.Derived.ZetaContinuationWitnessUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_functional_factor_nonescape [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name eta'
      analytic' transports' zeroLedger' gamma' functionalRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg →
      Cont basic eta' analytic' →
        Cont analytic' functional transports' →
          Cont pole zeroLedger' gamma' →
            hsame eta eta' →
              hsame zeroLedger zeroLedger' →
                UnaryHistory routes →
                  UnaryHistory name →
                    Cont routes name functionalRead →
                      PkgSig bundle functionalRead pkg →
                        hsame analytic analytic' ∧ hsame transports transports' ∧
                          hsame gamma gamma' ∧ UnaryHistory functionalRead ∧
                            hsame functionalRead (append routes name) ∧
                              PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
                                PkgSig bundle functionalRead pkg ∧
                                  (Cont functionalRead (BHist.e0 hostTail) routes → False) ∧
                                    (Cont functionalRead (BHist.e1 hostTail) routes →
                                      False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet basicRoute functionalRoute gammaRoute etaSame zeroLedgerSame routesUnary
    nameUnary routesNameFunctional functionalPkg
  obtain ⟨basicEtaAnalytic, analyticFunctionalTransports, poleZeroLedgerGamma,
    _transportsRoutesProvenance, namePkg, provenancePkg⟩ := packet
  have analyticSame : hsame analytic analytic' :=
    cont_respects_hsame (hsame_refl basic) etaSame basicEtaAnalytic basicRoute
  have transportsSame : hsame transports transports' :=
    cont_respects_hsame analyticSame (hsame_refl functional) analyticFunctionalTransports
      functionalRoute
  have gammaSame : hsame gamma gamma' :=
    cont_respects_hsame (hsame_refl pole) zeroLedgerSame poleZeroLedgerGamma gammaRoute
  have functionalUnary : UnaryHistory functionalRead :=
    unary_cont_closed routesUnary nameUnary routesNameFunctional
  have e0Refusal : Cont functionalRead (BHist.e0 hostTail) routes → False :=
    fun back => cont_mutual_extension_right_tail_absurd.left routesNameFunctional back
  have e1Refusal : Cont functionalRead (BHist.e1 hostTail) routes → False :=
    fun back => cont_mutual_extension_right_tail_absurd.right routesNameFunctional back
  exact
    ⟨analyticSame, transportsSame, gammaSame, functionalUnary, routesNameFunctional,
      namePkg, provenancePkg, functionalPkg, e0Refusal, e1Refusal⟩

end BEDC.Derived.ZetaContinuationWitnessUp
