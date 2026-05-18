import BEDC.Derived.AuthorizedGeneratorRecursorUp.TasteGate

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRootBranchAuditCoupling [AskSetup] [PackageSetup]
    {signature eliminator branches descent output audit routes name branchRead publicRead outputRead
      auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont signature eliminator branches ->
      Cont branches descent branchRead ->
        Cont branchRead routes publicRead ->
          Cont output audit outputRead ->
            Cont outputRead name auditRead ->
              hsame descent BHist.Empty ->
                UnaryHistory signature ->
                  UnaryHistory eliminator ->
                    UnaryHistory branches ->
                      UnaryHistory routes ->
                        UnaryHistory output ->
                          UnaryHistory audit ->
                            UnaryHistory name ->
                              PkgSig bundle name pkg ->
                                UnaryHistory publicRead ∧ UnaryHistory auditRead ∧
                                  Cont signature eliminator branches ∧
                                    Cont branches descent branchRead ∧
                                      Cont branchRead routes publicRead ∧
                                        Cont output audit outputRead ∧
                                          Cont outputRead name auditRead ∧
                                            SemanticNameCert
                                              (fun row : BHist =>
                                                hsame row name ∧ UnaryHistory row)
                                              (fun row : BHist =>
                                                hsame row name ∧
                                                  Cont branches descent branchRead ∧
                                                    Cont output audit outputRead ∧
                                                      Cont outputRead name auditRead)
                                              (fun row : BHist =>
                                                hsame row name ∧ PkgSig bundle name pkg)
                                              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro signatureEliminatorBranches branchesDescentBranchRead branchReadRoutesPublicRead
    outputAuditOutputRead outputReadNameAuditRead descentEmpty _signatureUnary _eliminatorUnary
    branchesUnary routesUnary outputUnary auditUnary nameUnary namePkg
  have descentUnary : UnaryHistory descent :=
    unary_transport unary_empty (hsame_symm descentEmpty)
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed branchesUnary descentUnary branchesDescentBranchRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed branchReadUnary routesUnary branchReadRoutesPublicRead
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed outputUnary auditUnary outputAuditOutputRead
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed outputReadUnary nameUnary outputReadNameAuditRead
  have sourceName : (fun row : BHist => hsame row name ∧ UnaryHistory row) name := by
    exact ⟨hsame_refl name, nameUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row name ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row name ∧ Cont branches descent branchRead ∧
            Cont output audit outputRead ∧ Cont outputRead name auditRead)
        (fun row : BHist => hsame row name ∧ PkgSig bundle name pkg)
        hsame := {
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
        ⟨source.left, branchesDescentBranchRead, outputAuditOutputRead,
          outputReadNameAuditRead⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, namePkg⟩
  }
  exact
    ⟨publicReadUnary, auditReadUnary, signatureEliminatorBranches,
      branchesDescentBranchRead, branchReadRoutesPublicRead, outputAuditOutputRead,
      outputReadNameAuditRead, cert⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
