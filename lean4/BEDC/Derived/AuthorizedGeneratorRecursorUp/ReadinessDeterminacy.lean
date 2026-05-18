import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorReadinessDeterminacy [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N outputRead outputRead' publicRead publicRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont D O outputRead -> Cont D O outputRead' ->
        Cont outputRead C publicRead -> Cont outputRead' C publicRead' ->
          PkgSig bundle publicRead pkg -> PkgSig bundle publicRead' pkg ->
            hsame outputRead outputRead' ∧ hsame publicRead publicRead' ∧
              UnaryHistory publicRead ∧ UnaryHistory publicRead' ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier dOOutput dOOutput' outputPublic outputPublic' _publicPkg _publicPkg'
  obtain ⟨_iUnary, _eUnary, _mUnary, _bUnary, dUnary, oUnary, _aUnary, _hUnary,
    cUnary, _pUnary, _gUnary, _nUnary, _iEM, _mBD, _dOA, _hAC, pPkg⟩ := carrier
  have sameOutput : hsame outputRead outputRead' :=
    cont_deterministic dOOutput dOOutput'
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed (unary_cont_closed dUnary oUnary dOOutput) cUnary outputPublic
  have publicReadUnary' : UnaryHistory publicRead' :=
    unary_cont_closed (unary_cont_closed dUnary oUnary dOOutput') cUnary outputPublic'
  have transportedPublic : Cont outputRead C publicRead' := by
    cases sameOutput
    exact outputPublic'
  have samePublic : hsame publicRead publicRead' :=
    cont_deterministic outputPublic transportedPublic
  exact ⟨sameOutput, samePublic, publicReadUnary, publicReadUnary', pPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
