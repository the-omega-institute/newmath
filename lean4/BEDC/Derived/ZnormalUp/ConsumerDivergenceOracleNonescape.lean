import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_consumer_divergence_oracle_nonescape [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name
      terminalRead normalRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminalRead →
        Cont terminalRead normal normalRead →
          Cont normalRead routes consumer →
            PkgSig bundle consumer pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row typed ∨ hsame row fuel ∨ hsame row terminalRead ∨
                      hsame row normal ∨ hsame row normalRead ∨ hsame row consumer)
                  (fun row : BHist => hsame row consumer ∧ PkgSig bundle consumer pkg)
                  hsame ∧
                PkgSig bundle provenance pkg ∧ UnaryHistory consumer := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet typedFuelTerminalRead terminalReadNormalRead normalReadRoutesConsumer
    consumerPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, _continuationUnary,
    _transportsUnary, routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalRead
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed normalReadUnary routesUnary normalReadRoutesConsumer
  have consumerSource :
      (fun row : BHist => hsame row consumer ∧ UnaryHistory row) consumer := by
    exact ⟨hsame_refl consumer, consumerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row typed ∨ hsame row fuel ∨ hsame row terminalRead ∨
              hsame row normal ∨ hsame row normalRead ∨ hsame row consumer)
          (fun row : BHist => hsame row consumer ∧ PkgSig bundle consumer pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro consumer consumerSource
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
          intro row row' sameRows source
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro row source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
      ledger_sound := by
        intro row source
        exact ⟨source.left, consumerPkg⟩
    }
  exact ⟨cert, provenancePkg, consumerUnary⟩

end BEDC.Derived.ZnormalUp
