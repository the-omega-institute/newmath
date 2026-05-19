import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_host_conversion_nonescape [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead
      hostRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminalRead →
        Cont terminalRead normal hostRead →
          Cont hostRead transports consumer →
            PkgSig bundle consumer pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row typed ∨ hsame row terminalRead ∨ hsame row hostRead ∨
                      hsame row consumer)
                  (fun row : BHist =>
                    hsame row consumer ∧ PkgSig bundle consumer pkg)
                  hsame ∧
                hsame terminalRead terminal ∧ hsame hostRead continuation ∧
                  UnaryHistory consumer ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet typedFuelTerminalRead terminalReadNormalHostRead hostReadTransportsConsumer
    consumerPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, _continuationUnary,
    transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have hostReadSame : hsame hostRead continuation :=
    cont_respects_hsame terminalReadSame (hsame_refl normal)
      terminalReadNormalHostRead terminalNormalContinuation
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have hostReadUnary : UnaryHistory hostRead :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalHostRead
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed hostReadUnary transportsUnary hostReadTransportsConsumer
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row typed ∨ hsame row terminalRead ∨ hsame row hostRead ∨
              hsame row consumer)
          (fun row : BHist => hsame row consumer ∧ PkgSig bundle consumer pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro consumer ⟨hsame_refl consumer, consumerUnary⟩
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, consumerPkg⟩
  }
  exact ⟨cert, terminalReadSame, hostReadSame, consumerUnary, provenancePkg⟩

end BEDC.Derived.ZnormalUp
