import BEDC.Derived.AuthorizedGeneratorRecursorUp.TasteGate
import BEDC.FKernel.Package

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursor_root_output_consumer_triad [AskSetup] [PackageSetup]
    {signature eliminator motive branches descent output audit transport routes provenance gap name
      tailRead outputRead auditRead boundaryRead rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont signature eliminator branches ->
      Cont branches descent tailRead ->
        Cont output audit outputRead ->
          Cont outputRead name auditRead ->
            Cont gap name boundaryRead ->
              Cont auditRead boundaryRead rootRead ->
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
                                    PkgSig bundle provenance pkg ->
                                      PkgSig bundle rootRead pkg ->
                                        UnaryHistory tailRead ∧ UnaryHistory outputRead ∧
                                          UnaryHistory auditRead ∧ UnaryHistory boundaryRead ∧
                                            UnaryHistory rootRead ∧
                                              Cont signature eliminator branches ∧
                                                Cont branches descent tailRead ∧
                                                  Cont output audit outputRead ∧
                                                    Cont outputRead name auditRead ∧
                                                      Cont gap name boundaryRead ∧
                                                        Cont auditRead boundaryRead rootRead ∧
                                                          PkgSig bundle provenance pkg ∧
                                                            PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro signatureEliminatorBranches branchesDescentTailRead outputAuditOutputRead
    outputReadNameAuditRead gapNameBoundaryRead auditBoundaryRootRead descentEmpty
    _signatureUnary _eliminatorUnary _motiveUnary branchesUnary _routesUnary outputUnary
    auditUnary gapUnary nameUnary provenancePkg rootPkg
  have descentUnary : UnaryHistory descent :=
    unary_transport unary_empty (hsame_symm descentEmpty)
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed branchesUnary descentUnary branchesDescentTailRead
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed outputUnary auditUnary outputAuditOutputRead
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed outputReadUnary nameUnary outputReadNameAuditRead
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed gapUnary nameUnary gapNameBoundaryRead
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed auditReadUnary boundaryReadUnary auditBoundaryRootRead
  exact
    ⟨tailReadUnary, outputReadUnary, auditReadUnary, boundaryReadUnary, rootReadUnary,
      signatureEliminatorBranches, branchesDescentTailRead, outputAuditOutputRead,
      outputReadNameAuditRead, gapNameBoundaryRead, auditBoundaryRootRead, provenancePkg,
      rootPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
