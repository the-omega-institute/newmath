import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_root_total_host_obligation_package [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name
      terminalRead rootRead downstream normalwordRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminalRead →
        Cont terminalRead normal rootRead →
          Cont rootRead transports downstream →
            Cont normal continuation normalwordRead →
              PkgSig bundle downstream pkg →
                PkgSig bundle normalwordRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row downstream ∨ hsame row normalwordRead)
                      (fun _row : BHist =>
                        Cont typed fuel terminalRead ∧ Cont terminalRead normal rootRead ∧
                          Cont rootRead transports downstream ∧
                            Cont normal continuation normalwordRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ PkgSig bundle name pkg ∧
                          PkgSig bundle provenance pkg)
                      hsame ∧
                    UnaryHistory terminalRead ∧ UnaryHistory rootRead ∧
                      UnaryHistory downstream ∧ UnaryHistory normalwordRead ∧
                        PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet typedFuelTerminalRead terminalNormalRootRead rootTransportsDownstream
    normalContinuationNormalword downstreamPkg normalwordPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, continuationUnary,
    transportsUnary, _routesUnary, provenanceUnary, nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, namePkg, provenancePkg⟩ :=
    packet
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed terminalReadUnary normalUnary terminalNormalRootRead
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed rootReadUnary transportsUnary rootTransportsDownstream
  have normalwordUnary : UnaryHistory normalwordRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationNormalword
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row downstream ∨ hsame row normalwordRead)
          (fun _row : BHist =>
            Cont typed fuel terminalRead ∧ Cont terminalRead normal rootRead ∧
              Cont rootRead transports downstream ∧ Cont normal continuation normalwordRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro downstream (Or.inl (hsame_refl downstream))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        cases source with
        | inl sameDownstream =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameDownstream)
        | inr sameNormalword =>
            exact Or.inr (hsame_trans (hsame_symm sameRows) sameNormalword)
    }
    pattern_sound := by
      intro _row _source
      exact
        ⟨typedFuelTerminalRead, terminalNormalRootRead, rootTransportsDownstream,
          normalContinuationNormalword⟩
    ledger_sound := by
      intro _row source
      cases source with
      | inl sameDownstream =>
          exact
            ⟨unary_transport downstreamUnary (hsame_symm sameDownstream), namePkg,
              provenancePkg⟩
      | inr sameNormalword =>
          exact
            ⟨unary_transport normalwordUnary (hsame_symm sameNormalword), namePkg,
              provenancePkg⟩
  }
  exact
    ⟨cert, terminalReadUnary, rootReadUnary, downstreamUnary, normalwordUnary, namePkg,
      provenancePkg⟩

end BEDC.Derived.ZnormalUp
