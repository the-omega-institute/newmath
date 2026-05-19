import BEDC.Derived.AuthorizedGeneratorRecursorUp.TasteGate

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursor_l10_output_authorization_closure
    {signature eliminator motive branches descent output audit transport routes provenance gap name
      outputRead publicRead boundaryRead : BHist} :
    Cont output audit outputRead →
      Cont outputRead routes publicRead →
        Cont gap name boundaryRead →
          UnaryHistory output →
            UnaryHistory audit →
              UnaryHistory routes →
                UnaryHistory gap →
                  UnaryHistory name →
                    authorizedGeneratorRecursorFromEventFlow
                        (authorizedGeneratorRecursorToEventFlow
                          (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches
                            descent output audit transport routes provenance gap name)) =
                      some
                        (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches
                          descent output audit transport routes provenance gap name) ∧
                      UnaryHistory outputRead ∧ UnaryHistory publicRead ∧
                        UnaryHistory boundaryRead ∧ Cont output audit outputRead ∧
                          Cont outputRead routes publicRead ∧
                            Cont gap name boundaryRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro outputAuditRead outputReadRoutesPublic gapNameBoundary outputUnary auditUnary
    routesUnary gapUnary nameUnary
  have roundTrip :
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
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed outputUnary auditUnary outputAuditRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed outputReadUnary routesUnary outputReadRoutesPublic
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed gapUnary nameUnary gapNameBoundary
  exact
    ⟨roundTrip, outputReadUnary, publicReadUnary, boundaryReadUnary, outputAuditRead,
      outputReadRoutesPublic, gapNameBoundary⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
