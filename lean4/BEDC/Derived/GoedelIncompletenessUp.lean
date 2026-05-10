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

theorem GoedelIncompletenessWitnessPacket_undecidable_row_obligation
    [AskSetup] [PackageSetup]
    {axiomEnum proofChecker formulaRow goedelNumber provabilityRow fixedPointRow noProofRow
      noRefutationRow verdictLedger syntaxLedger endpoint provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GoedelIncompletenessWitnessPacket axiomEnum proofChecker formulaRow goedelNumber
      provabilityRow fixedPointRow noProofRow noRefutationRow verdictLedger syntaxLedger endpoint
      provenance bundle pkg ->
        UnaryHistory noProofRow ∧ UnaryHistory noRefutationRow ∧ UnaryHistory syntaxLedger ∧
          UnaryHistory endpoint ∧ hsame syntaxLedger (append noProofRow noRefutationRow) ∧
            hsame endpoint (append fixedPointRow verdictLedger) ∧
              SigRel bundle endpoint provenance ∧ PkgSig bundle provenance pkg := by
  intro packet
  have verdictUnary : UnaryHistory verdictLedger :=
    unary_cont_closed packet.left packet.right.left
      packet.right.right.right.right.right.right.right.left
  have syntaxUnary : UnaryHistory syntaxLedger :=
    unary_cont_closed packet.right.right.right.right.right.left
      packet.right.right.right.right.right.right.left
      packet.right.right.right.right.right.right.right.right.right.left
  have fixedPointUnary : UnaryHistory fixedPointRow :=
    unary_cont_closed packet.right.right.left packet.right.right.right.left
      packet.right.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed fixedPointUnary verdictUnary
      packet.right.right.right.right.right.right.right.right.right.right.left
  exact
    ⟨packet.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.left,
      syntaxUnary,
      endpointUnary,
      packet.right.right.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.right.right.right.right⟩

theorem GoedelIncompletenessWitnessPacket_fixed_point_obligation
    [AskSetup] [PackageSetup]
    {axiomEnum proofChecker formulaRow transportedFormula goedelNumber provabilityRow
      fixedPointRow transportedFixedPoint noProofRow noRefutationRow verdictLedger
      syntaxLedger endpoint transportedEndpoint provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GoedelIncompletenessWitnessPacket axiomEnum proofChecker formulaRow goedelNumber
      provabilityRow fixedPointRow noProofRow noRefutationRow verdictLedger syntaxLedger endpoint
      provenance bundle pkg ->
        hsame formulaRow transportedFormula ->
          Cont transportedFormula goedelNumber transportedFixedPoint ->
            Cont transportedFixedPoint verdictLedger transportedEndpoint ->
              UnaryHistory transportedFixedPoint ∧
                UnaryHistory transportedEndpoint ∧
                  hsame transportedFixedPoint fixedPointRow ∧
                    hsame transportedEndpoint endpoint ∧
                      SigRel bundle endpoint provenance ∧ PkgSig bundle provenance pkg := by
  intro packet formulaTransport fixedPointTransport endpointTransport
  have transportedFormulaUnary : UnaryHistory transportedFormula :=
    unary_transport packet.right.right.left formulaTransport
  have transportedFixedPointUnary : UnaryHistory transportedFixedPoint :=
    unary_cont_closed transportedFormulaUnary packet.right.right.right.left fixedPointTransport
  have verdictUnary : UnaryHistory verdictLedger :=
    unary_cont_closed packet.left packet.right.left
      packet.right.right.right.right.right.right.right.left
  have transportedEndpointUnary : UnaryHistory transportedEndpoint :=
    unary_cont_closed transportedFixedPointUnary verdictUnary endpointTransport
  have fixedPointSame : hsame transportedFixedPoint fixedPointRow :=
    cont_respects_hsame (hsame_symm formulaTransport) (hsame_refl goedelNumber)
      fixedPointTransport packet.right.right.right.right.right.right.right.right.left
  have endpointSame : hsame transportedEndpoint endpoint :=
    cont_respects_hsame fixedPointSame (hsame_refl verdictLedger) endpointTransport
      packet.right.right.right.right.right.right.right.right.right.right.left
  exact And.intro transportedFixedPointUnary
    (And.intro transportedEndpointUnary
      (And.intro fixedPointSame
        (And.intro endpointSame
          (And.intro packet.right.right.right.right.right.right.right.right.right.right.right.left
            packet.right.right.right.right.right.right.right.right.right.right.right.right))))

end BEDC.Derived.GoedelIncompletenessUp
