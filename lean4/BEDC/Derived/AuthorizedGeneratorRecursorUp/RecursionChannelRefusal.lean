import BEDC.Derived.AuthorizedGeneratorRecursorUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRecursionChannelRefusal [AskSetup] [PackageSetup]
    {signature eliminator motive branches descent output audit transport routes provenance gap name
      branchRead outputRead auditRead boundaryRead refusedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont signature eliminator branches ->
      Cont branches descent branchRead ->
        Cont output audit outputRead ->
          Cont outputRead routes auditRead ->
            Cont gap name boundaryRead ->
              Cont boundaryRead auditRead refusedRead ->
                hsame transport BHist.Empty ->
                  UnaryHistory signature ->
                    UnaryHistory eliminator ->
                      UnaryHistory branches ->
                        UnaryHistory descent ->
                          UnaryHistory output ->
                            UnaryHistory audit ->
                              UnaryHistory routes ->
                                UnaryHistory gap ->
                                  UnaryHistory name ->
                                    PkgSig bundle provenance pkg ->
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row refusedRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            Cont boundaryRead auditRead refusedRead ∧
                                              hsame row refusedRead)
                                          (fun row : BHist =>
                                            PkgSig bundle provenance pkg ∧
                                              hsame row refusedRead)
                                          hsame ∧
                                        UnaryHistory refusedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro _signatureEliminatorBranches _branchesDescentBranchRead outputAuditOutputRead
    outputReadRoutesAuditRead gapNameBoundaryRead boundaryAuditRefused _transportEmpty
    _signatureUnary _eliminatorUnary _branchesUnary _descentUnary outputUnary auditUnary
    routesUnary gapUnary nameUnary provenancePkg
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed outputUnary auditUnary outputAuditOutputRead
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed outputReadUnary routesUnary outputReadRoutesAuditRead
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed gapUnary nameUnary gapNameBoundaryRead
  have refusedUnary : UnaryHistory refusedRead :=
    unary_cont_closed boundaryReadUnary auditReadUnary boundaryAuditRefused
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row refusedRead ∧ UnaryHistory row)
        (fun row : BHist =>
          Cont boundaryRead auditRead refusedRead ∧ hsame row refusedRead)
        (fun row : BHist => PkgSig bundle provenance pkg ∧ hsame row refusedRead)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro refusedRead (And.intro (hsame_refl refusedRead) refusedUnary)
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
        exact
          And.intro (hsame_trans (hsame_symm sameRows) source.left)
            (unary_transport source.right sameRows)
    }
    pattern_sound := by
      intro _row source
      exact And.intro boundaryAuditRefused source.left
    ledger_sound := by
      intro _row source
      exact And.intro provenancePkg source.left
  }
  exact And.intro cert refusedUnary

end BEDC.Derived.AuthorizedGeneratorRecursorUp
