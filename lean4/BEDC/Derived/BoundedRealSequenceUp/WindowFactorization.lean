import BEDC.Derived.BoundedRealSequenceUp.NameCertObligations

namespace BEDC.Derived.BoundedRealSequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedRealSequenceCarrier_window_factorization [AskSetup] [PackageSetup]
    {S W Q R I H C P N windowRead readbackRead sealRead boundRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NameCertObligations.BoundedRealSequenceCarrier S W Q R I H C P N bundle pkg →
      Cont S W windowRead →
        Cont windowRead Q readbackRead →
          Cont readbackRead R sealRead →
            Cont sealRead I boundRead →
              PkgSig bundle boundRead pkg →
                UnaryHistory windowRead ∧ UnaryHistory readbackRead ∧
                  UnaryHistory sealRead ∧ UnaryHistory boundRead ∧
                    Cont S W windowRead ∧ Cont windowRead Q readbackRead ∧
                      Cont readbackRead R sealRead ∧ Cont sealRead I boundRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier sourceWindow windowReadback readbackSeal sealBound _boundPkg
  obtain ⟨sourceUnary, windowUnary, readbackUnary, realUnary, intervalUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localCertUnary, _intervalRoute,
    _transportSame, _provenancePkg, _localCertPkg⟩ := carrier
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed sourceUnary windowUnary sourceWindow
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowReadUnary readbackUnary windowReadback
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackReadUnary realUnary readbackSeal
  have boundReadUnary : UnaryHistory boundRead :=
    unary_cont_closed sealReadUnary intervalUnary sealBound
  exact
    ⟨windowReadUnary, readbackReadUnary, sealReadUnary, boundReadUnary, sourceWindow,
      windowReadback, readbackSeal, sealBound⟩

end BEDC.Derived.BoundedRealSequenceUp
