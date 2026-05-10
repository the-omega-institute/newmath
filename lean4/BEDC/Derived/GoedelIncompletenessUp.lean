import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.GoedelIncompletenessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem GoedelIncompletenessProofCheckerLedger_verdict_nonempty_surface
    {axiomEnum decoder proofRow verdict proofLedger syntaxLedger sourceSurface tail : BHist} :
    UnaryHistory axiomEnum -> UnaryHistory decoder -> UnaryHistory proofRow ->
      UnaryHistory verdict -> Cont axiomEnum decoder proofLedger ->
        Cont proofRow verdict syntaxLedger -> Cont proofLedger syntaxLedger sourceSurface ->
          hsame verdict (BHist.e1 tail) ->
            UnaryHistory proofLedger ∧ UnaryHistory syntaxLedger ∧ UnaryHistory sourceSurface ∧
              hsame proofLedger (append axiomEnum decoder) ∧
                hsame syntaxLedger (append proofRow verdict) ∧
                  hsame sourceSurface (append proofLedger syntaxLedger) ∧
                    (hsame verdict BHist.Empty -> False) := by
  intro axiomUnary decoderUnary proofUnary verdictUnary proofLedgerRow syntaxLedgerRow
    sourceSurfaceRow verdictE1
  have proofLedgerUnary : UnaryHistory proofLedger :=
    unary_cont_closed axiomUnary decoderUnary proofLedgerRow
  have syntaxLedgerUnary : UnaryHistory syntaxLedger :=
    unary_cont_closed proofUnary verdictUnary syntaxLedgerRow
  have sourceSurfaceUnary : UnaryHistory sourceSurface :=
    unary_cont_closed proofLedgerUnary syntaxLedgerUnary sourceSurfaceRow
  have verdictNonempty : hsame verdict BHist.Empty -> False := by
    intro verdictEmpty
    exact not_hsame_e1_empty (hsame_trans (hsame_symm verdictE1) verdictEmpty)
  exact And.intro proofLedgerUnary
    (And.intro syntaxLedgerUnary
      (And.intro sourceSurfaceUnary
        (And.intro proofLedgerRow
          (And.intro syntaxLedgerRow
            (And.intro sourceSurfaceRow verdictNonempty)))))

end BEDC.Derived.GoedelIncompletenessUp
