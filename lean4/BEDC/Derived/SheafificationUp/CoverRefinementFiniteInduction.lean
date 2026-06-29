import BEDC.Derived.SheafificationUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.SheafificationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SheafificationCoverRefinementFiniteInduction [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N baseRefine stepRefine localityRead gluingRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg →
      Cont C T baseRefine →
      Cont baseRefine J stepRefine →
      Cont stepRefine P localityRead →
      Cont localityRead G gluingRead →
      PkgSig bundle gluingRead pkg →
      UnaryHistory baseRefine ∧ UnaryHistory stepRefine ∧ UnaryHistory localityRead ∧
        UnaryHistory gluingRead ∧ Cont C T baseRefine ∧
        Cont baseRefine J stepRefine ∧ Cont stepRefine P localityRead ∧
        Cont localityRead G gluingRead ∧ PkgSig bundle N pkg ∧
        PkgSig bundle gluingRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier baseRoute stepRoute localityRoute gluingRoute gluingPkg
  obtain ⟨cUnary, tUnary, jUnary, pUnary, _lUnary, gUnary, _sUnary, _hUnary,
    _rUnary, _qUnary, _nUnary, _qPkg, nPkg⟩ := carrier
  have baseUnary : UnaryHistory baseRefine :=
    unary_cont_closed cUnary tUnary baseRoute
  have stepUnary : UnaryHistory stepRefine :=
    unary_cont_closed baseUnary jUnary stepRoute
  have localityUnary : UnaryHistory localityRead :=
    unary_cont_closed stepUnary pUnary localityRoute
  have gluingUnary : UnaryHistory gluingRead :=
    unary_cont_closed localityUnary gUnary gluingRoute
  exact
    ⟨baseUnary, stepUnary, localityUnary, gluingUnary, baseRoute, stepRoute,
      localityRoute, gluingRoute, nPkg, gluingPkg⟩

end BEDC.Derived.SheafificationUp
