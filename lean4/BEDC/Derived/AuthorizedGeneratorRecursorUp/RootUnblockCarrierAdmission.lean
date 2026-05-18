import BEDC.Derived.AuthorizedGeneratorRecursorUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow

theorem AuthorizedGeneratorRecursorRootUnblockCarrierAdmission
    {signature eliminator motive branches descent output audit transport routes provenance gap name
      branchRead outputRead publicRead : BHist} :
    Cont signature eliminator branches ->
      Cont branches descent branchRead ->
        Cont output audit outputRead ->
          Cont outputRead routes publicRead ->
            hsame transport BHist.Empty ->
              UnaryHistory signature ->
                UnaryHistory eliminator ->
                  UnaryHistory branches ->
                    UnaryHistory descent ->
                      UnaryHistory output ->
                        UnaryHistory audit ->
                          UnaryHistory routes ->
                            authorizedGeneratorRecursorFromEventFlow
                                (authorizedGeneratorRecursorToEventFlow
                                  (AuthorizedGeneratorRecursorUp.mk signature eliminator motive
                                    branches descent output audit transport routes provenance gap
                                    name)) =
                              some
                                (AuthorizedGeneratorRecursorUp.mk signature eliminator motive
                                  branches descent output audit transport routes provenance gap
                                  name) ∧
                              UnaryHistory branchRead ∧ UnaryHistory outputRead ∧
                                UnaryHistory publicRead ∧ Cont signature eliminator branches ∧
                                  Cont branches descent branchRead ∧
                                    Cont output audit outputRead ∧
                                      Cont outputRead routes publicRead ∧
                                        hsame transport BHist.Empty ∧
                                          authorizedGeneratorRecursorEncodeBHist BHist.Empty =
                                            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame UnaryHistory
  intro signatureEliminatorBranches branchesDescentBranchRead outputAuditOutputRead
    outputReadRoutesPublicRead transportEmpty _signatureUnary _eliminatorUnary branchesUnary
    descentUnary outputUnary auditUnary routesUnary
  have routeRoundTrip :
      authorizedGeneratorRecursorFromEventFlow
          (authorizedGeneratorRecursorToEventFlow
            (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches descent output
              audit transport routes provenance gap name)) =
        some
          (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches descent output
            audit transport routes provenance gap name) :=
    AuthorizedGeneratorRecursorTasteGate_single_carrier_alignment.right.left
      (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches descent output audit
        transport routes provenance gap name)
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed branchesUnary descentUnary branchesDescentBranchRead
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed outputUnary auditUnary outputAuditOutputRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed outputReadUnary routesUnary outputReadRoutesPublicRead
  exact
    ⟨routeRoundTrip, branchReadUnary, outputReadUnary, publicReadUnary,
      signatureEliminatorBranches, branchesDescentBranchRead, outputAuditOutputRead,
      outputReadRoutesPublicRead, transportEmpty, rfl⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
