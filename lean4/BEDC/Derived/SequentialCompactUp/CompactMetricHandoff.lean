import BEDC.Derived.SequentialCompactUp.ObligationReadiness

namespace BEDC.Derived.SequentialCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialCompactCompactMetricHandoff [AskSetup] [PackageSetup]
    {K B S W R E H C P N compactRead windowRead regularRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialCompactCarrier K B S W R E H C P N bundle pkg →
      Cont K B compactRead →
        Cont compactRead W windowRead →
          Cont windowRead R regularRead →
            PkgSig bundle regularRead pkg →
              UnaryHistory compactRead ∧ UnaryHistory windowRead ∧
                UnaryHistory regularRead ∧ Cont K B compactRead ∧
                  Cont compactRead W windowRead ∧ Cont windowRead R regularRead ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle regularRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier compactRoute windowRoute regularRoute regularPkg
  obtain ⟨unaryK, unaryB, _unaryS, unaryW, unaryR, _unaryE, _unaryH, _unaryC,
    _unaryP, _unaryN, _compactBaireStream, _streamWindowRegular,
      _regularSealTransport, _transportReplayProvenance, provenancePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed unaryK unaryB compactRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed compactUnary unaryW windowRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed windowUnary unaryR regularRoute
  exact
    ⟨compactUnary, windowUnary, regularUnary, compactRoute, windowRoute, regularRoute,
      provenancePkg, regularPkg⟩

end BEDC.Derived.SequentialCompactUp
