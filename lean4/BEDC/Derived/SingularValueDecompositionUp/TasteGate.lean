import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SingularValueDecompositionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SingularValueDecompositionCarrier [AskSetup] [PackageSetup]
    (A U V D L R F Q T H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory A ∧ UnaryHistory U ∧ UnaryHistory V ∧ UnaryHistory D ∧
    UnaryHistory L ∧ UnaryHistory R ∧ UnaryHistory F ∧ UnaryHistory Q ∧
      UnaryHistory T ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
        UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem SingularValueDecompositionFiniteMatrixHandoff [AskSetup] [PackageSetup]
    {A U V D L R F Q T H C P N matrixRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SingularValueDecompositionCarrier A U V D L R F Q T H C P N bundle pkg →
      Cont A L matrixRead →
        PkgSig bundle matrixRead pkg →
          UnaryHistory A ∧ UnaryHistory U ∧ UnaryHistory V ∧ UnaryHistory D ∧
            UnaryHistory L ∧ UnaryHistory matrixRead ∧ Cont A L matrixRead ∧
              PkgSig bundle N pkg ∧ PkgSig bundle matrixRead pkg := by
  -- BEDC touchpoint anchor: SingularValueDecompositionCarrier BHist Cont PkgSig UnaryHistory
  intro carrier matrixRoute matrixPkg
  obtain ⟨aUnary, uUnary, vUnary, dUnary, lUnary, _rUnary, _fUnary, _qUnary,
    _tUnary, _hUnary, _cUnary, _pUnary, _nUnary, _provenancePkg, namePkg⟩ := carrier
  have matrixUnary : UnaryHistory matrixRead :=
    unary_cont_closed aUnary lUnary matrixRoute
  exact
    ⟨aUnary, uUnary, vUnary, dUnary, lUnary, matrixUnary, matrixRoute, namePkg,
      matrixPkg⟩

end BEDC.Derived.SingularValueDecompositionUp
