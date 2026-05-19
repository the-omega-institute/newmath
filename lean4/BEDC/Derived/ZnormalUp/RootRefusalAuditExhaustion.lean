import BEDC.Derived.ZnormalUp.RootRefusalLedgerSeparation

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_root_refusal_audit_exhaustion [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead rootRead
      downstream consumer hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminalRead →
        Cont terminalRead normal rootRead →
          Cont rootRead transports downstream →
            Cont downstream routes consumer →
              PkgSig bundle consumer pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row typed ∨ hsame row terminalRead ∨ hsame row rootRead ∨
                        hsame row downstream ∨ hsame row consumer)
                    (fun row : BHist => hsame row consumer ∧ PkgSig bundle consumer pkg)
                    hsame ∧
                  hsame terminalRead terminal ∧ hsame rootRead continuation ∧
                    UnaryHistory terminalRead ∧ UnaryHistory rootRead ∧
                      UnaryHistory downstream ∧ UnaryHistory consumer ∧
                        Cont typed fuel terminalRead ∧ Cont terminalRead normal rootRead ∧
                          Cont rootRead transports downstream ∧ Cont downstream routes consumer ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg ∧
                              (Cont consumer (BHist.e0 hostTail) typed → False) ∧
                                (Cont consumer (BHist.e1 hostTail) typed → False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet typedFuelTerminalRead terminalReadNormalRootRead rootReadTransportsDownstream
    downstreamRoutesConsumer consumerPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, _continuationUnary,
    transportsUnary, routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have terminalReadSame : hsame terminalRead terminal :=
    cont_respects_hsame (hsame_refl typed) (hsame_refl fuel) typedFuelTerminalRead
      typedFuelTerminal
  have rootReadSame : hsame rootRead continuation :=
    cont_respects_hsame terminalReadSame (hsame_refl normal) terminalReadNormalRootRead
      terminalNormalContinuation
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalRootRead
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed rootReadUnary transportsUnary rootReadTransportsDownstream
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed downstreamUnary routesUnary downstreamRoutesConsumer
  have typedToConsumer : Cont typed (append fuel (append normal (append transports routes)))
      consumer := by
    cases typedFuelTerminalRead
    cases terminalReadNormalRootRead
    cases rootReadTransportsDownstream
    cases downstreamRoutesConsumer
    exact (append_assoc (append (append typed fuel) normal) transports routes).trans
      ((append_assoc (append typed fuel) normal (append transports routes)).trans
        (append_assoc typed fuel (append normal (append transports routes))))
  have e0Refusal : Cont consumer (BHist.e0 hostTail) typed → False :=
    fun back => cont_mutual_extension_right_tail_absurd.left typedToConsumer back
  have e1Refusal : Cont consumer (BHist.e1 hostTail) typed → False :=
    fun back => cont_mutual_extension_right_tail_absurd.right typedToConsumer back
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row typed ∨ hsame row terminalRead ∨ hsame row rootRead ∨
            hsame row downstream ∨ hsame row consumer)
        (fun row : BHist => hsame row consumer ∧ PkgSig bundle consumer pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro consumer ⟨hsame_refl consumer, consumerUnary⟩
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
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, consumerPkg⟩
  }
  exact
    ⟨cert, terminalReadSame, rootReadSame, terminalReadUnary, rootReadUnary,
      downstreamUnary, consumerUnary, typedFuelTerminalRead, terminalReadNormalRootRead,
      rootReadTransportsDownstream, downstreamRoutesConsumer, provenancePkg, consumerPkg,
      e0Refusal, e1Refusal⟩

end BEDC.Derived.ZnormalUp
