import BEDC.Derived.SheafificationUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.SheafificationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SheafificationLocalityGluingLedgerReadiness [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N sourceRead localityRead gluingRead targetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg ->
      Cont C T sourceRead ->
        Cont P L localityRead ->
          Cont localityRead G gluingRead ->
            Cont gluingRead S targetRead ->
              PkgSig bundle targetRead pkg ->
                UnaryHistory sourceRead ∧ UnaryHistory localityRead ∧
                  UnaryHistory gluingRead ∧ UnaryHistory targetRead ∧
                    Cont C T sourceRead ∧ Cont P L localityRead ∧
                      Cont localityRead G gluingRead ∧ Cont gluingRead S targetRead ∧
                        PkgSig bundle Q pkg ∧ PkgSig bundle N pkg ∧
                          PkgSig bundle targetRead pkg := by
  -- BEDC touchpoint anchor: SheafificationCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier sourceRoute localityRoute gluingRoute targetRoute targetPkg
  obtain ⟨cUnary, tUnary, _jUnary, pUnary, lUnary, gUnary, sUnary, _hUnary, _rUnary,
    _qUnary, _nUnary, qPkg, nPkg⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed cUnary tUnary sourceRoute
  have localityUnary : UnaryHistory localityRead :=
    unary_cont_closed pUnary lUnary localityRoute
  have gluingUnary : UnaryHistory gluingRead :=
    unary_cont_closed localityUnary gUnary gluingRoute
  have targetUnary : UnaryHistory targetRead :=
    unary_cont_closed gluingUnary sUnary targetRoute
  exact
    ⟨sourceUnary, localityUnary, gluingUnary, targetUnary, sourceRoute, localityRoute,
      gluingRoute, targetRoute, qPkg, nPkg, targetPkg⟩

end BEDC.Derived.SheafificationUp
