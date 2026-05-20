import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_terminal_readback_semantic_certificate [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminal →
        Cont terminal continuation terminalRead →
          PkgSig bundle name pkg →
            SemanticNameCert
              (fun row : BHist =>
                ZnormalPacket typed fuel terminal normal continuation transports routes
                    provenance name bundle pkg ∧
                  (hsame row typed ∨ hsame row fuel ∨ hsame row terminal ∨
                    hsame row terminalRead))
              (fun _row : BHist =>
                Cont typed fuel terminal ∧ Cont terminal continuation terminalRead)
              (fun row : BHist => UnaryHistory row ∨ PkgSig bundle name pkg)
              hsame := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro packet typedFuelTerminal terminalContinuationRead _namePkg
  have packetWitness := packet
  obtain ⟨typedUnary, fuelUnary, terminalUnary, _normalUnary, continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _packetNamePkg,
    _provenancePkg⟩ := packet
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed terminalUnary continuationUnary terminalContinuationRead
  exact {
    core := {
      carrier_inhabited := by
        exact ⟨typed, packetWitness, Or.inl (hsame_refl typed)⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _row' leftSame rightSame
        exact hsame_trans leftSame rightSame
      carrier_respects_equiv := by
        intro _row _row' same source
        constructor
        · exact source.left
        · cases source.right with
          | inl sameTyped =>
              exact Or.inl (hsame_trans (hsame_symm same) sameTyped)
          | inr rest =>
              cases rest with
              | inl sameFuel =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm same) sameFuel))
              | inr rest =>
                  cases rest with
                  | inl sameTerminal =>
                      exact Or.inr
                        (Or.inr (Or.inl (hsame_trans (hsame_symm same) sameTerminal)))
                  | inr sameTerminalRead =>
                      exact Or.inr
                        (Or.inr
                          (Or.inr (hsame_trans (hsame_symm same) sameTerminalRead)))
    }
    pattern_sound := by
      intro _row _source
      exact ⟨typedFuelTerminal, terminalContinuationRead⟩
    ledger_sound := by
      intro _row source
      cases source.right with
      | inl sameTyped =>
          exact Or.inl (unary_transport typedUnary (hsame_symm sameTyped))
      | inr rest =>
          cases rest with
          | inl sameFuel =>
              exact Or.inl (unary_transport fuelUnary (hsame_symm sameFuel))
          | inr rest =>
              cases rest with
              | inl sameTerminal =>
                  exact Or.inl (unary_transport terminalUnary (hsame_symm sameTerminal))
              | inr sameTerminalRead =>
                  exact Or.inl
                    (unary_transport terminalReadUnary (hsame_symm sameTerminalRead))
  }

end BEDC.Derived.ZnormalUp
