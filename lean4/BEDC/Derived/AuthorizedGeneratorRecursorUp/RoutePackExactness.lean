import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier
import BEDC.FKernel.NameCert

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRoutePackExactness [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N branchRead descentRead outputRead publicRead
      boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont I E branchRead -> Cont branchRead D descentRead ->
        Cont descentRead O outputRead -> Cont outputRead C publicRead ->
          Cont G N boundaryRead -> PkgSig bundle publicRead pkg ->
            SemanticNameCert
              (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row publicRead ∧ Cont I E branchRead ∧
                Cont branchRead D descentRead ∧ Cont descentRead O outputRead ∧
                  Cont outputRead C row ∧ Cont G N boundaryRead)
              (fun row : BHist => hsame row publicRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle publicRead pkg)
              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier branchRoute descentRoute outputRoute publicRoute boundaryRoute publicPkg
  obtain ⟨iUnary, eUnary, _mUnary, _bUnary, dUnary, oUnary, _aUnary, _hUnary,
    cUnary, _pUnary, gUnary, nUnary, _iEM, _mBD, _dOA, _hAC, pPkg⟩ := carrier
  have branchUnary : UnaryHistory branchRead :=
    unary_cont_closed iUnary eUnary branchRoute
  have descentUnary : UnaryHistory descentRead :=
    unary_cont_closed branchUnary dUnary descentRoute
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed descentUnary oUnary outputRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed outputUnary cUnary publicRoute
  have sourcePublic :
      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row) publicRead := by
    exact ⟨hsame_refl publicRead, publicUnary⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro publicRead sourcePublic
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact ⟨hsame_trans (hsame_symm sameRows) source.left,
          unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro row source
      exact ⟨source.left, branchRoute, descentRoute, outputRoute,
        cont_result_hsame_transport publicRoute (hsame_symm source.left), boundaryRoute⟩
    ledger_sound := by
      intro row source
      exact ⟨source.left, pPkg, publicPkg⟩
  }

end BEDC.Derived.AuthorizedGeneratorRecursorUp
