import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary

namespace BEDC.Derived.GoedelIncompletenessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
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

theorem GoedelIncompletenessFixedPointLedger_obligation
    {formula numbering proofChecker provability fixedPoint ledger : BHist} :
    UnaryHistory formula ->
      UnaryHistory numbering ->
        UnaryHistory proofChecker ->
          Cont formula numbering fixedPoint ->
            Cont proofChecker fixedPoint provability ->
              Cont fixedPoint provability ledger ->
                UnaryHistory fixedPoint ∧ UnaryHistory provability ∧ UnaryHistory ledger ∧
                  hsame fixedPoint (append formula numbering) ∧
                    hsame provability (append proofChecker fixedPoint) ∧
                      hsame ledger (append fixedPoint provability) := by
  intro formulaUnary numberingUnary proofCheckerUnary fixedPointRow provabilityRow ledgerRow
  have fixedPointUnary : UnaryHistory fixedPoint :=
    unary_cont_closed formulaUnary numberingUnary fixedPointRow
  have provabilityUnary : UnaryHistory provability :=
    unary_cont_closed proofCheckerUnary fixedPointUnary provabilityRow
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed fixedPointUnary provabilityUnary ledgerRow
  constructor
  · exact fixedPointUnary
  constructor
  · exact provabilityUnary
  constructor
  · exact ledgerUnary
  constructor
  · exact fixedPointRow
  constructor
  · exact provabilityRow
  · exact ledgerRow

def GoedelIncompletenessWitnessPacket [AskSetup] [PackageSetup]
    (axiomEnum proofChecker formulaRow goedelNumber provabilityRow fixedPointRow noProofRow
      noRefutationRow verdictLedger syntaxLedger endpoint provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory axiomEnum ∧
    UnaryHistory proofChecker ∧
      UnaryHistory formulaRow ∧
        UnaryHistory goedelNumber ∧
          UnaryHistory provabilityRow ∧
            UnaryHistory noProofRow ∧
              UnaryHistory noRefutationRow ∧
                Cont axiomEnum proofChecker verdictLedger ∧
                  Cont formulaRow goedelNumber fixedPointRow ∧
                    Cont noProofRow noRefutationRow syntaxLedger ∧
                      Cont fixedPointRow verdictLedger endpoint ∧
                        SigRel bundle endpoint provenance ∧
                          PkgSig bundle provenance pkg

theorem GoedelIncompletenessWitnessPacket_proof_checker_obligation
    [AskSetup] [PackageSetup]
    {axiomEnum proofChecker formulaRow goedelNumber provabilityRow fixedPointRow noProofRow
      noRefutationRow verdictLedger syntaxLedger endpoint provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GoedelIncompletenessWitnessPacket axiomEnum proofChecker formulaRow goedelNumber
      provabilityRow fixedPointRow noProofRow noRefutationRow verdictLedger syntaxLedger endpoint
      provenance bundle pkg ->
        UnaryHistory verdictLedger ∧
          UnaryHistory fixedPointRow ∧
            UnaryHistory syntaxLedger ∧
              UnaryHistory endpoint ∧
                hsame verdictLedger (append axiomEnum proofChecker) ∧
                  hsame fixedPointRow (append formulaRow goedelNumber) ∧
                    hsame syntaxLedger (append noProofRow noRefutationRow) ∧
                      hsame endpoint (append fixedPointRow verdictLedger) ∧
                        SigRel bundle endpoint provenance ∧
                          PkgSig bundle provenance pkg := by
  intro packet
  have verdictUnary : UnaryHistory verdictLedger :=
    unary_cont_closed packet.left packet.right.left
      packet.right.right.right.right.right.right.right.left
  have fixedPointUnary : UnaryHistory fixedPointRow :=
    unary_cont_closed packet.right.right.left packet.right.right.right.left
      packet.right.right.right.right.right.right.right.right.left
  have syntaxUnary : UnaryHistory syntaxLedger :=
    unary_cont_closed packet.right.right.right.right.right.left
      packet.right.right.right.right.right.right.left
      packet.right.right.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed fixedPointUnary verdictUnary
      packet.right.right.right.right.right.right.right.right.right.right.left
  exact And.intro verdictUnary
    (And.intro fixedPointUnary
      (And.intro syntaxUnary
        (And.intro endpointUnary
          (And.intro packet.right.right.right.right.right.right.right.left
            (And.intro packet.right.right.right.right.right.right.right.right.left
              (And.intro packet.right.right.right.right.right.right.right.right.right.left
                (And.intro packet.right.right.right.right.right.right.right.right.right.right.left
                  (And.intro
                    packet.right.right.right.right.right.right.right.right.right.right.right.left
                    packet.right.right.right.right.right.right.right.right.right.right.right.right))))))))

end BEDC.Derived.GoedelIncompletenessUp
