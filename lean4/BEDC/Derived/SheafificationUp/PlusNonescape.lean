import BEDC.Derived.SheafificationUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.SheafificationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SheafificationPlusNonescape [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N plusRead gluingRead targetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg →
      Cont L G plusRead →
        Cont plusRead S gluingRead →
          Cont gluingRead R targetRead →
            PkgSig bundle targetRead pkg →
              UnaryHistory L ∧ UnaryHistory G ∧ UnaryHistory S ∧
                UnaryHistory plusRead ∧ UnaryHistory gluingRead ∧
                  UnaryHistory targetRead ∧ Cont L G plusRead ∧
                    Cont plusRead S gluingRead ∧ Cont gluingRead R targetRead ∧
                      PkgSig bundle targetRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier plusRoute gluingRoute targetRoute targetPkg
  obtain ⟨_cUnary, _tUnary, _jUnary, _pUnary, lUnary, gUnary, sUnary, _hUnary,
    rUnary, _qUnary, _nUnary, _qPkg, _namePkg⟩ := carrier
  have plusUnary : UnaryHistory plusRead :=
    unary_cont_closed lUnary gUnary plusRoute
  have gluingUnary : UnaryHistory gluingRead :=
    unary_cont_closed plusUnary sUnary gluingRoute
  have targetUnary : UnaryHistory targetRead :=
    unary_cont_closed gluingUnary rUnary targetRoute
  exact
    ⟨lUnary, gUnary, sUnary, plusUnary, gluingUnary, targetUnary, plusRoute,
      gluingRoute, targetRoute, targetPkg⟩

end BEDC.Derived.SheafificationUp
