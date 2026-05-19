import BEDC.Derived.AuthorizedGeneratorRecursorUp.TasteGate

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRootBoundaryNonescape [AskSetup] [PackageSetup]
    {signature eliminator motive branches descent output audit _transport routes provenance gap name
      branchRead publicRead outputRoute auditRoute boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont signature eliminator branches ->
      Cont branches descent branchRead ->
        Cont branchRead routes publicRead ->
          hsame descent BHist.Empty ->
            UnaryHistory signature ->
              UnaryHistory eliminator ->
                UnaryHistory motive ->
                  UnaryHistory branches ->
                    UnaryHistory routes ->
                      UnaryHistory output ->
                        UnaryHistory audit ->
                          UnaryHistory gap ->
                            UnaryHistory name ->
                              Cont output audit outputRoute ->
                                Cont outputRoute name auditRoute ->
                                  Cont gap name boundaryRead ->
                                    PkgSig bundle provenance pkg ->
                                      UnaryHistory publicRead ∧ UnaryHistory boundaryRead ∧
                                        Cont signature eliminator branches ∧
                                          Cont branches descent branchRead ∧
                                            Cont branchRead routes publicRead ∧
                                              Cont output audit outputRoute ∧
                                                Cont outputRoute name auditRoute ∧
                                                  Cont gap name boundaryRead ∧
                                                    SemanticNameCert
                                                      (fun row : BHist =>
                                                        hsame row name ∧ UnaryHistory row)
                                                      (fun row : BHist =>
                                                        hsame row name ∧
                                                          Cont output audit outputRoute ∧
                                                            Cont outputRoute name auditRoute ∧
                                                              Cont gap name boundaryRead)
                                                      (fun row : BHist =>
                                                        hsame row name ∧
                                                          PkgSig bundle provenance pkg)
                                                      hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro signatureEliminatorBranches branchesDescentBranchRead branchReadRoutesPublicRead
    descentEmpty _signatureUnary _eliminatorUnary _motiveUnary branchesUnary routesUnary
    outputUnary auditUnary gapUnary nameUnary outputAuditRoute outputRouteNameAuditRoute
    gapNameBoundaryRead provenancePkg
  have descentUnary : UnaryHistory descent :=
    unary_transport unary_empty (hsame_symm descentEmpty)
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed branchesUnary descentUnary branchesDescentBranchRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed branchReadUnary routesUnary branchReadRoutesPublicRead
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed gapUnary nameUnary gapNameBoundaryRead
  have sourceName : (fun row : BHist => hsame row name ∧ UnaryHistory row) name := by
    exact ⟨hsame_refl name, nameUnary⟩
  exact
    ⟨publicReadUnary, boundaryReadUnary, signatureEliminatorBranches,
      branchesDescentBranchRead, branchReadRoutesPublicRead, outputAuditRoute,
      outputRouteNameAuditRoute, gapNameBoundaryRead,
      {
        core := {
          carrier_inhabited := Exists.intro name sourceName
          equiv_refl := by
            intro row _source
            exact hsame_refl row
          equiv_symm := by
            intro _row _other same
            exact hsame_symm same
          equiv_trans := by
            intro _row _middle _other sameLeft sameRight
            exact hsame_trans sameLeft sameRight
          carrier_respects_equiv := by
            intro _row _other same source
            exact
              ⟨hsame_trans (hsame_symm same) source.left,
                unary_transport source.right same⟩
        }
        pattern_sound := by
          intro _row source
          exact
            ⟨source.left, outputAuditRoute, outputRouteNameAuditRoute,
              gapNameBoundaryRead⟩
        ledger_sound := by
          intro _row source
          exact ⟨source.left, provenancePkg⟩
      }⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
