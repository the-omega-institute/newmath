import BEDC.Derived.SheafificationUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.SheafificationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SheafificationCoverRefinementBudget [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N baseRefine stepRefine localityRead gluingRead targetRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg →
      Cont C T baseRefine →
        Cont baseRefine J stepRefine →
          Cont stepRefine P localityRead →
            Cont localityRead G gluingRead →
              Cont gluingRead S targetRead →
                PkgSig bundle targetRead pkg →
                  UnaryHistory baseRefine ∧ UnaryHistory stepRefine ∧
                    UnaryHistory localityRead ∧ UnaryHistory gluingRead ∧
                      UnaryHistory targetRead ∧ Cont C T baseRefine ∧
                        Cont baseRefine J stepRefine ∧ Cont stepRefine P localityRead ∧
                          Cont localityRead G gluingRead ∧ Cont gluingRead S targetRead ∧
                            PkgSig bundle Q pkg ∧ PkgSig bundle N pkg ∧
                              PkgSig bundle targetRead pkg := by
  -- BEDC touchpoint anchor: SheafificationCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier baseRoute stepRoute localityRoute gluingRoute targetRoute targetPkg
  obtain ⟨cUnary, tUnary, jUnary, pUnary, _lUnary, gUnary, sUnary, _hUnary,
    _rUnary, _qUnary, _nUnary, provenancePkg, namePkg⟩ := carrier
  have baseUnary : UnaryHistory baseRefine :=
    unary_cont_closed cUnary tUnary baseRoute
  have stepUnary : UnaryHistory stepRefine :=
    unary_cont_closed baseUnary jUnary stepRoute
  have localityUnary : UnaryHistory localityRead :=
    unary_cont_closed stepUnary pUnary localityRoute
  have gluingUnary : UnaryHistory gluingRead :=
    unary_cont_closed localityUnary gUnary gluingRoute
  have targetUnary : UnaryHistory targetRead :=
    unary_cont_closed gluingUnary sUnary targetRoute
  exact
    ⟨baseUnary, stepUnary, localityUnary, gluingUnary, targetUnary, baseRoute,
      stepRoute, localityRoute, gluingRoute, targetRoute, provenancePkg, namePkg,
      targetPkg⟩

end BEDC.Derived.SheafificationUp
