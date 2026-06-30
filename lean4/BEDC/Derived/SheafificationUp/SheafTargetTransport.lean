import BEDC.Derived.SheafificationUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.SheafificationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SheafificationSheafTargetTransport [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N gluingRead targetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg →
      Cont P L gluingRead →
        Cont gluingRead S targetRead →
          PkgSig bundle targetRead pkg →
            UnaryHistory gluingRead ∧ UnaryHistory targetRead ∧ Cont P L gluingRead ∧
              Cont gluingRead S targetRead ∧ PkgSig bundle Q pkg ∧ PkgSig bundle N pkg ∧
                PkgSig bundle targetRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier gluingRoute targetRoute targetPkg
  obtain ⟨_cUnary, _tUnary, _jUnary, pUnary, lUnary, _gUnary, sUnary, _hUnary,
    _rUnary, _qUnary, _nUnary, qPkg, nPkg⟩ := carrier
  have gluingUnary : UnaryHistory gluingRead :=
    unary_cont_closed pUnary lUnary gluingRoute
  have targetUnary : UnaryHistory targetRead :=
    unary_cont_closed gluingUnary sUnary targetRoute
  exact
    ⟨gluingUnary, targetUnary, gluingRoute, targetRoute, qPkg, nPkg, targetPkg⟩

end BEDC.Derived.SheafificationUp
