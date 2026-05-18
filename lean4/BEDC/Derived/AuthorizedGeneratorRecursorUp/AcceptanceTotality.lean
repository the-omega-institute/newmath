import BEDC.Derived.AuthorizedGeneratorRecursorUp.TasteGate

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorCarrier_acceptance_totality
    {signature eliminator motive branches descent output audit transport routes provenance gap name
      branchRead descentRead outputRead publicRead : BHist} :
    authorizedGeneratorRecursorFromEventFlow
        (authorizedGeneratorRecursorToEventFlow
          (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches descent output audit
            transport routes provenance gap name)) =
        some
          (AuthorizedGeneratorRecursorUp.mk signature eliminator motive branches descent output audit
            transport routes provenance gap name) →
      Cont signature eliminator branches →
        Cont branches descent branchRead →
          Cont motive descent descentRead →
            Cont branchRead descentRead outputRead →
              Cont outputRead routes publicRead →
                UnaryHistory branches →
                  UnaryHistory descent →
                    UnaryHistory motive →
                      UnaryHistory routes →
                        UnaryHistory branchRead ∧ UnaryHistory descentRead ∧
                          UnaryHistory outputRead ∧ UnaryHistory publicRead ∧
                            Cont branches descent branchRead ∧
                              Cont motive descent descentRead ∧
                                Cont branchRead descentRead outputRead ∧
                                  Cont outputRead routes publicRead ∧
                                    authorizedGeneratorRecursorEncodeBHist BHist.Empty =
                                      ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark Cont UnaryHistory
  intro _roundTrip _signatureEliminatorBranches branchesDescentBranchRead
    motiveDescentDescentRead branchDescentOutputRead outputRoutesPublicRead branchesUnary
    descentUnary motiveUnary routesUnary
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed branchesUnary descentUnary branchesDescentBranchRead
  have descentReadUnary : UnaryHistory descentRead :=
    unary_cont_closed motiveUnary descentUnary motiveDescentDescentRead
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed branchReadUnary descentReadUnary branchDescentOutputRead
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed outputReadUnary routesUnary outputRoutesPublicRead
  exact
    ⟨branchReadUnary, descentReadUnary, outputReadUnary, publicReadUnary,
      branchesDescentBranchRead, motiveDescentDescentRead, branchDescentOutputRead,
      outputRoutesPublicRead, rfl⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
