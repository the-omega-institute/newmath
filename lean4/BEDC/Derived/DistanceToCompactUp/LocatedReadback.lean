import BEDC.Derived.DistanceToCompactUp.TasteGate

namespace BEDC.Derived.DistanceToCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DistanceToCompactCarrier_located_readback [AskSetup] [PackageSetup]
    {X K L F R E H C P N compactRead locatedRead readbackRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DistanceToCompactCarrier X K L F R E H C P N bundle pkg →
      Cont X K compactRead →
        Cont compactRead L locatedRead →
          Cont locatedRead R readbackRead →
            Cont readbackRead E realRead →
              PkgSig bundle realRead pkg →
                UnaryHistory compactRead ∧ UnaryHistory locatedRead ∧
                  UnaryHistory readbackRead ∧ UnaryHistory realRead ∧
                    PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier compactRoute locatedRoute readbackRoute realRoute realPkg
  obtain ⟨xUnary, kUnary, lUnary, _fUnary, rUnary, eUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _provenancePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed xUnary kUnary compactRoute
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed compactUnary lUnary locatedRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed locatedUnary rUnary readbackRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed readbackUnary eUnary realRoute
  exact ⟨compactUnary, locatedUnary, readbackUnary, realUnary, realPkg⟩

end BEDC.Derived.DistanceToCompactUp
