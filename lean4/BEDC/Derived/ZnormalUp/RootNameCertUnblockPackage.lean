import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalRootNameCertUnblockPackage [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name sourceRead
      sourceExport terminalRead rootRead downstream : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont typed fuel sourceRead ->
        Cont sourceRead name sourceExport ->
          Cont typed fuel terminalRead ->
            Cont terminalRead normal rootRead ->
              Cont rootRead transports downstream ->
                PkgSig bundle sourceExport pkg ->
                  PkgSig bundle downstream pkg ->
                    SemanticNameCert
                        (fun row : BHist =>
                          (hsame row sourceExport ∨ hsame row downstream) ∧
                            UnaryHistory row)
                        (fun row : BHist =>
                          hsame row typed ∨ hsame row fuel ∨ hsame row sourceRead ∨
                            hsame row sourceExport ∨ hsame row terminalRead ∨
                              hsame row rootRead ∨ hsame row downstream)
                        (fun row : BHist =>
                          (hsame row sourceExport ∨ hsame row downstream) ∧
                            (PkgSig bundle sourceExport pkg ∨
                              PkgSig bundle downstream pkg))
                        hsame ∧
                      hsame terminalRead terminal ∧ hsame rootRead continuation ∧
                        UnaryHistory sourceRead ∧ UnaryHistory sourceExport ∧
                          UnaryHistory terminalRead ∧ UnaryHistory rootRead ∧
                            UnaryHistory downstream ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet typedFuelSourceRead sourceReadNameSourceExport typedFuelTerminalRead
    terminalReadNormalRootRead rootReadTransportsDownstream sourceExportPkg downstreamPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, _continuationUnary,
    transportsUnary, _routesUnary, _provenanceUnary, nameUnary, typedFuelTerminal,
    terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelSourceRead
  have sourceExportUnary : UnaryHistory sourceExport :=
    unary_cont_closed sourceReadUnary nameUnary sourceReadNameSourceExport
  have terminalReadSame : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have rootReadSame : hsame rootRead continuation :=
    cont_respects_hsame terminalReadSame (hsame_refl normal)
      terminalReadNormalRootRead terminalNormalContinuation
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed terminalReadUnary normalUnary terminalReadNormalRootRead
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed rootReadUnary transportsUnary rootReadTransportsDownstream
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row sourceExport ∨ hsame row downstream) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row typed ∨ hsame row fuel ∨ hsame row sourceRead ∨
              hsame row sourceExport ∨ hsame row terminalRead ∨ hsame row rootRead ∨
                hsame row downstream)
          (fun row : BHist =>
            (hsame row sourceExport ∨ hsame row downstream) ∧
              (PkgSig bundle sourceExport pkg ∨ PkgSig bundle downstream pkg))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sourceExport
        ⟨Or.inl (hsame_refl sourceExport), sourceExportUnary⟩
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
        constructor
        · cases source.left with
          | inl sameSource =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameSource)
          | inr sameDownstream =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameDownstream)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameSource =>
          exact Or.inr (Or.inr (Or.inr (Or.inl sameSource)))
      | inr sameDownstream =>
          exact Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr sameDownstream)))))
    ledger_sound := by
      intro _row source
      cases source.left with
      | inl sameSource =>
          exact ⟨Or.inl sameSource, Or.inl sourceExportPkg⟩
      | inr sameDownstream =>
          exact ⟨Or.inr sameDownstream, Or.inr downstreamPkg⟩
  }
  exact
    ⟨cert, terminalReadSame, rootReadSame, sourceReadUnary, sourceExportUnary,
      terminalReadUnary, rootReadUnary, downstreamUnary, provenancePkg⟩

end BEDC.Derived.ZnormalUp
