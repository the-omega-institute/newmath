import BEDC.Derived.AuthorizedGeneratorRecursorUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorHostKernelHandoff [AskSetup] [PackageSetup]
    {signature eliminator motive branches descent output audit transport routes provenance gap name
      branchRead publicRead outputRoute auditRoute : BHist}
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
                          UnaryHistory name ->
                            Cont output audit outputRoute ->
                              Cont outputRoute name auditRoute ->
                                PkgSig bundle provenance pkg ->
                                  UnaryHistory publicRead ∧
                                    Cont signature eliminator branches ∧
                                      Cont branches descent branchRead ∧
                                        Cont branchRead routes publicRead ∧
                                          hsame descent BHist.Empty ∧
                                            SemanticNameCert
                                              (fun row : BHist =>
                                                hsame row name ∧ UnaryHistory row)
                                              (fun row : BHist =>
                                                hsame row name ∧
                                                  Cont output audit outputRoute ∧
                                                    Cont outputRoute name auditRoute)
                                              (fun row : BHist =>
                                                hsame row name ∧ PkgSig bundle provenance pkg)
                                              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro signatureEliminatorBranches branchesDescentBranchRead branchReadRoutesPublicRead
    descentEmpty signatureUnary eliminatorUnary _motiveUnary branchesUnary routesUnary outputUnary
    auditUnary nameUnary outputAuditRoute outputRouteNameAuditRoute provenancePkg
  have branchExhausted :
      UnaryHistory publicRead ∧ Cont signature eliminator branches ∧
        Cont branches descent branchRead ∧
          Cont branchRead routes publicRead ∧ hsame descent BHist.Empty :=
    AuthorizedGeneratorRecursorBranchExhaustion signatureEliminatorBranches
      branchesDescentBranchRead branchReadRoutesPublicRead descentEmpty signatureUnary eliminatorUnary
      branchesUnary routesUnary
  have outputRouteUnary : UnaryHistory outputRoute :=
    unary_cont_closed outputUnary auditUnary outputAuditRoute
  have _auditRouteUnary : UnaryHistory auditRoute :=
    unary_cont_closed outputRouteUnary nameUnary outputRouteNameAuditRoute
  have _transportSelf : hsame transport transport := hsame_refl transport
  have _gapSelf : hsame gap gap := hsame_refl gap
  have sourceName : (fun row : BHist => hsame row name ∧ UnaryHistory row) name := by
    exact ⟨hsame_refl name, nameUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row name ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row name ∧ Cont output audit outputRoute ∧ Cont outputRoute name auditRoute)
        (fun row : BHist => hsame row name ∧ PkgSig bundle provenance pkg)
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
          ⟨hsame_trans (hsame_symm same) source.left, unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, outputAuditRoute, outputRouteNameAuditRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg⟩
  }
  exact
    ⟨branchExhausted.left, branchExhausted.right.left, branchExhausted.right.right.left,
      branchExhausted.right.right.right.left, branchExhausted.right.right.right.right, cert⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
