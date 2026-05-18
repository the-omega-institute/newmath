import BEDC.Derived.ZetaContinuationWitnessUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_eta_denominator_boundary [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name etaRead
      hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg →
      UnaryHistory eta →
        UnaryHistory transports →
          Cont eta transports etaRead →
            PkgSig bundle etaRead pkg →
              UnaryHistory etaRead ∧ hsame etaRead (append eta transports) ∧
                Cont basic eta analytic ∧ Cont analytic functional transports ∧
                  PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle etaRead pkg ∧
                      (Cont etaRead (BHist.e0 hostTail) eta → False) ∧
                        (Cont etaRead (BHist.e1 hostTail) eta → False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro packet etaUnary transportsUnary etaTransportsRead etaReadPkg
  obtain ⟨basicEtaAnalytic, analyticFunctionalTransports, _poleZeroLedgerGamma,
    _transportsRoutesProvenance, namePkg, provenancePkg⟩ := packet
  have etaReadUnary : UnaryHistory etaRead :=
    unary_cont_closed etaUnary transportsUnary etaTransportsRead
  have e0Refusal : Cont etaRead (BHist.e0 hostTail) eta → False :=
    fun back => cont_mutual_extension_right_tail_absurd.left etaTransportsRead back
  have e1Refusal : Cont etaRead (BHist.e1 hostTail) eta → False :=
    fun back => cont_mutual_extension_right_tail_absurd.right etaTransportsRead back
  exact
    ⟨etaReadUnary, etaTransportsRead, basicEtaAnalytic, analyticFunctionalTransports,
      namePkg, provenancePkg, etaReadPkg, e0Refusal, e1Refusal⟩

end BEDC.Derived.ZetaContinuationWitnessUp
