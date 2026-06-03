import BEDC.Derived.BoundedRealSequenceUp.NameCertObligations

namespace BEDC.Derived.BoundedRealSequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedRealSequenceCarrier_finite_window_net_extraction [AskSetup] [PackageSetup]
    {S W Q R I H C P N windowRead readbackRead boundRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NameCertObligations.BoundedRealSequenceCarrier S W Q R I H C P N bundle pkg →
      Cont S W windowRead →
        Cont windowRead Q readbackRead →
          Cont readbackRead R boundRead →
            PkgSig bundle boundRead pkg →
              UnaryHistory windowRead ∧ UnaryHistory readbackRead ∧
                UnaryHistory boundRead ∧ Cont S W windowRead ∧
                  Cont windowRead Q readbackRead ∧ Cont readbackRead R boundRead ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle boundRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier sourceWindow windowReadback readbackBound boundPkg
  obtain ⟨sourceUnary, windowUnary, readbackUnary, realUnary, _intervalUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localCertUnary, _intervalRoute,
    _transportSame, provenancePkg, _localCertPkg⟩ := carrier
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed sourceUnary windowUnary sourceWindow
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowReadUnary readbackUnary windowReadback
  have boundReadUnary : UnaryHistory boundRead :=
    unary_cont_closed readbackReadUnary realUnary readbackBound
  exact
    ⟨windowReadUnary, readbackReadUnary, boundReadUnary, sourceWindow, windowReadback,
      readbackBound, provenancePkg, boundPkg⟩

end BEDC.Derived.BoundedRealSequenceUp
