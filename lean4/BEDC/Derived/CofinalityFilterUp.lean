import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CofinalityFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CofinalityFilterCarrier [AskSetup] [PackageSetup]
    (I L B F U E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig NameCert
  UnaryHistory I ∧ UnaryHistory L ∧ UnaryHistory B ∧ UnaryHistory F ∧ UnaryHistory U ∧
    UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
      PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem CofinalityFilterCarrier_tail_cobase_handoff [AskSetup] [PackageSetup]
    {I L B F U E H C P N tailCobase filterRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofinalityFilterCarrier I L B F U E H C P N bundle pkg →
      Cont I L tailCobase →
        Cont tailCobase B filterRead →
          Cont filterRead F completionRead →
            PkgSig bundle completionRead pkg →
              UnaryHistory I ∧ UnaryHistory L ∧ UnaryHistory B ∧ UnaryHistory F ∧
                UnaryHistory tailCobase ∧ UnaryHistory filterRead ∧
                  UnaryHistory completionRead ∧ Cont I L tailCobase ∧
                    Cont tailCobase B filterRead ∧ Cont filterRead F completionRead ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier tailRoute filterRoute completionRoute completionPkg
  obtain ⟨iUnary, lUnary, bUnary, fUnary, _uUnary, _eUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, pPkg, _nPkg⟩ := carrier
  have tailUnary : UnaryHistory tailCobase :=
    unary_cont_closed iUnary lUnary tailRoute
  have filterUnary : UnaryHistory filterRead :=
    unary_cont_closed tailUnary bUnary filterRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed filterUnary fUnary completionRoute
  exact
    ⟨iUnary, lUnary, bUnary, fUnary, tailUnary, filterUnary, completionUnary, tailRoute,
      filterRoute, completionRoute, pPkg, completionPkg⟩

end BEDC.Derived.CofinalityFilterUp
