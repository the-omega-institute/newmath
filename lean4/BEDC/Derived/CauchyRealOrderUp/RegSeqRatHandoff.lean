import BEDC.Derived.CauchyRealOrderUp

namespace BEDC.Derived.CauchyRealOrderUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyRealOrderCarrier_regseqrat_handoff [AskSetup] [PackageSetup]
    {sourceLeft sourceRight window dyadic quotient realSeal verdict transport replay provenance
      nameRow leftRead rightRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyRealOrderCarrier sourceLeft sourceRight window dyadic quotient realSeal verdict
        transport replay provenance nameRow bundle pkg →
      Cont sourceLeft window leftRead →
        Cont sourceRight window rightRead →
          Cont quotient realSeal sealRead →
            PkgSig bundle provenance pkg →
              UnaryHistory sourceLeft ∧ UnaryHistory sourceRight ∧ UnaryHistory window ∧
                UnaryHistory dyadic ∧ UnaryHistory quotient ∧ UnaryHistory realSeal ∧
                  UnaryHistory verdict ∧ UnaryHistory leftRead ∧ UnaryHistory rightRead ∧
                    UnaryHistory sealRead ∧ Cont sourceLeft sourceRight window ∧
                      Cont window dyadic quotient ∧ Cont quotient realSeal verdict ∧
                        Cont sourceLeft window leftRead ∧ Cont sourceRight window rightRead ∧
                          Cont quotient realSeal sealRead ∧
                            PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier leftRoute rightRoute sealRoute provenancePkg'
  obtain ⟨sourceLeftUnary, sourceRightUnary, windowUnary, dyadicUnary, quotientUnary,
    realSealUnary, verdictUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _nameRowUnary, sourcePairWindow, windowDyadicQuotient, quotientRealVerdict,
    _transportReplayProvenance, _provenancePkg⟩ := carrier
  have leftUnary : UnaryHistory leftRead :=
    unary_cont_closed sourceLeftUnary windowUnary leftRoute
  have rightUnary : UnaryHistory rightRead :=
    unary_cont_closed sourceRightUnary windowUnary rightRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed quotientUnary realSealUnary sealRoute
  exact
    ⟨sourceLeftUnary, sourceRightUnary, windowUnary, dyadicUnary, quotientUnary,
      realSealUnary, verdictUnary, leftUnary, rightUnary, sealUnary, sourcePairWindow,
      windowDyadicQuotient, quotientRealVerdict, leftRoute, rightRoute, sealRoute,
      provenancePkg'⟩

end BEDC.Derived.CauchyRealOrderUp
