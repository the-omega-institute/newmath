import BEDC.Derived.TheorySelfClassifierUp.TasteGate

namespace BEDC.Derived.TheorySelfClassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TheorySelfClassifier_sibling_independence [AskSetup] [PackageSetup]
    {G E R P A L H C Q N siblingRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TheorySelfClassifierCarrier G E R P A L H C Q N bundle pkg ->
      Cont Q siblingRead N ->
        PkgSig bundle Q pkg ->
          UnaryHistory L ∧ UnaryHistory siblingRead ∧ Cont Q siblingRead N ∧
            PkgSig bundle Q pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier siblingRoute siblingPkg
  obtain ⟨_gUnary, _eUnary, _rUnary, _pUnary, _aUnary, lUnary, _hUnary, _cUnary,
    _qUnary, nUnary, _generatorEqualityRoute, _recursorPurityRoute, _classifierRoute,
    _provenancePkg⟩ := carrier
  have siblingUnary : UnaryHistory siblingRead :=
    ((unary_cont_iff_result_unary siblingRoute).mpr nUnary).right.left
  exact ⟨lUnary, siblingUnary, siblingRoute, siblingPkg⟩

end BEDC.Derived.TheorySelfClassifierUp
