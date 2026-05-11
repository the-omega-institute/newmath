import BEDC.Derived.SignedDigitStreamUp

namespace BEDC.Derived.SignedDigitStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
theorem SignedDigitStreamWindowPacket_prefix_consumer_invariance [AskSetup] [PackageSetup]
    {digit schedule carry provenance endpoint ledger prefixDigit prefixSchedule prefixCarry
      prefixEndpoint prefixLedger regRadius regWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SignedDigitStreamWindowPacket digit schedule carry provenance endpoint ledger bundle pkg ->
      hsame digit prefixDigit ->
        hsame schedule prefixSchedule ->
          Cont prefixDigit prefixSchedule prefixCarry ->
            Cont prefixCarry provenance prefixEndpoint ->
              Cont prefixEndpoint prefixSchedule prefixLedger ->
                PkgSig bundle prefixLedger pkg ->
                  UnaryHistory regRadius ->
                    Cont prefixEndpoint regRadius regWindow ->
                      PkgSig bundle regWindow pkg ->
                        SemanticNameCert
                          (fun row : BHist =>
                            SignedDigitStreamWindowPacket prefixDigit prefixSchedule
                              prefixCarry provenance prefixEndpoint prefixLedger bundle pkg ∧
                                (hsame row prefixLedger ∨ hsame row regWindow))
                          (fun row : BHist =>
                            SignedDigitStreamWindowPacket prefixDigit prefixSchedule
                              prefixCarry provenance prefixEndpoint prefixLedger bundle pkg ∧
                                (hsame row prefixLedger ∨ hsame row regWindow))
                          (fun row : BHist =>
                            SignedDigitStreamWindowPacket prefixDigit prefixSchedule
                              prefixCarry provenance prefixEndpoint prefixLedger bundle pkg ∧
                                (hsame row prefixLedger ∨ hsame row regWindow))
                          hsame := by
  intro packet sameDigit sameSchedule prefixCarryRow prefixEndpointRow prefixLedgerRow
  intro prefixPkg regRadiusUnary regWindowRow _regWindowPkg
  have transported :=
    SignedDigitStreamWindowPacket_window_transport packet sameDigit sameSchedule
      (hsame_refl provenance) prefixCarryRow prefixEndpointRow prefixLedgerRow prefixPkg
  have prefixPacket :
      SignedDigitStreamWindowPacket prefixDigit prefixSchedule prefixCarry provenance
        prefixEndpoint prefixLedger bundle pkg :=
    transported.left
  have prefixEndpointUnary : UnaryHistory prefixEndpoint :=
    prefixPacket.right.right.right.right.left
  have _regWindowUnary : UnaryHistory regWindow :=
    unary_cont_closed prefixEndpointUnary regRadiusUnary regWindowRow
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro regWindow (And.intro prefixPacket (Or.inr (hsame_refl regWindow)))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _left _right sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro left right sameRows sourceLeft
        constructor
        · exact sourceLeft.left
        · cases sourceLeft.right with
          | inl sameLedger =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameLedger)
          | inr sameWindow =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameWindow)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem SignedDigitStreamWindowPacket_prefix_truncation_stability [AskSetup]
    [PackageSetup]
    {digits schedule carry provenance endpoint hidden ledger prefixLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SignedDigitStreamPacket digits schedule carry provenance endpoint hidden ledger bundle pkg ->
      Cont endpoint schedule prefixLedger ->
        PkgSig bundle prefixLedger pkg ->
          SignedDigitStreamWindowPacket digits schedule carry provenance endpoint prefixLedger
              bundle pkg ∧
            hsame carry (append digits schedule) ∧
              hsame endpoint (append carry provenance) ∧
                hsame prefixLedger (append endpoint schedule) := by
  intro packet prefixRow prefixPkg
  obtain ⟨digitsUnary, scheduleUnary, provenanceUnary, _hiddenUnary, carryUnary,
    endpointUnary, _ledgerUnary, carryRow, endpointRow, _ledgerRow, _ledgerPkg⟩ := packet
  have prefixUnary : UnaryHistory prefixLedger :=
    unary_cont_closed endpointUnary scheduleUnary prefixRow
  have windowPacket :
      SignedDigitStreamWindowPacket digits schedule carry provenance endpoint prefixLedger
        bundle pkg :=
    ⟨digitsUnary, scheduleUnary, carryUnary, provenanceUnary, endpointUnary, prefixUnary,
      carryRow, endpointRow, prefixRow, prefixPkg⟩
  exact ⟨windowPacket, carryRow, endpointRow, prefixRow⟩

end BEDC.Derived.SignedDigitStreamUp
