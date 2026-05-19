import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalRootReadinessNameCertPackage [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name sourceRead sourceExport
      siblingRead terminalRead hostRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name bundle pkg →
      Cont typed fuel sourceRead →
        Cont sourceRead name sourceExport →
          Cont normal continuation siblingRead →
            Cont typed fuel terminalRead →
              Cont terminal routes hostRead →
                PkgSig bundle sourceExport pkg →
                  PkgSig bundle siblingRead pkg →
                    PkgSig bundle hostRead pkg →
                      SemanticNameCert
                          (fun row : BHist =>
                            (hsame row sourceExport ∨ hsame row siblingRead ∨
                              hsame row hostRead) ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row typed ∨ hsame row fuel ∨ hsame row sourceRead ∨
                              hsame row sourceExport ∨ hsame row normal ∨
                                hsame row continuation ∨ hsame row siblingRead ∨
                                  hsame row hostRead)
                          (fun row : BHist =>
                            (hsame row sourceExport ∨ hsame row siblingRead ∨
                              hsame row hostRead) ∧
                              (PkgSig bundle sourceExport pkg ∨
                                PkgSig bundle siblingRead pkg ∨ PkgSig bundle hostRead pkg))
                          hsame ∧
                        hsame terminalRead terminal ∧ UnaryHistory hostRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packet typedFuelSourceRead sourceReadNameExport normalContinuationSiblingRead
    typedFuelTerminalRead terminalRoutesHostRead sourceExportPkg siblingReadPkg hostReadPkg
  obtain ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary,
    _transportsUnary, routesUnary, _provenanceUnary, nameUnary, typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, _provenancePkg⟩ :=
    packet
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelSourceRead
  have sourceExportUnary : UnaryHistory sourceExport :=
    unary_cont_closed sourceReadUnary nameUnary sourceReadNameExport
  have siblingReadUnary : UnaryHistory siblingRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationSiblingRead
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have sameTerminalRead : hsame terminalRead terminal :=
    cont_deterministic typedFuelTerminalRead typedFuelTerminal
  have hostReadUnary : UnaryHistory hostRead :=
    unary_cont_closed terminalUnary routesUnary terminalRoutesHostRead
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro sourceExport
            (And.intro (Or.inl (hsame_refl sourceExport)) sourceExportUnary)
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro row row' sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro row row' row'' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro row row' sameRows sourceData
          constructor
          · cases sourceData.left with
            | inl sameSourceExport =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) sameSourceExport)
            | inr rest =>
                cases rest with
                | inl sameSiblingRead =>
                    exact Or.inr
                      (Or.inl (hsame_trans (hsame_symm sameRows) sameSiblingRead))
                | inr sameHostRead =>
                    exact Or.inr
                      (Or.inr (hsame_trans (hsame_symm sameRows) sameHostRead))
          · exact unary_transport sourceData.right sameRows
      }
      pattern_sound := by
        intro row sourceData
        cases sourceData.left with
        | inl sameSourceExport =>
            exact Or.inr
              (Or.inr
                (Or.inr
                  (Or.inl sameSourceExport)))
        | inr rest =>
            cases rest with
            | inl sameSiblingRead =>
                exact Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inl sameSiblingRead))))))
            | inr sameHostRead =>
                exact Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr sameHostRead))))))
      ledger_sound := by
        intro row sourceData
        constructor
        · exact sourceData.left
        · cases sourceData.left with
          | inl _sameSourceExport =>
              exact Or.inl sourceExportPkg
          | inr rest =>
              cases rest with
              | inl _sameSiblingRead =>
                  exact Or.inr (Or.inl siblingReadPkg)
              | inr _sameHostRead =>
                  exact Or.inr (Or.inr hostReadPkg)
    }
  · exact And.intro sameTerminalRead hostReadUnary

theorem ZnormalPacket_root_readiness_namecert_package [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name sourceRead
      sourceExport siblingRead terminalRead downstream : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel sourceRead →
        Cont sourceRead name sourceExport →
          Cont normal continuation siblingRead →
            Cont typed fuel terminalRead →
              Cont terminalRead continuation downstream →
                PkgSig bundle sourceExport pkg →
                  PkgSig bundle siblingRead pkg →
                    PkgSig bundle downstream pkg →
                      SemanticNameCert
                        (fun row : BHist =>
                          (hsame row sourceExport ∨ hsame row siblingRead ∨
                            hsame row downstream) ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row typed ∨ hsame row fuel ∨ hsame row sourceRead ∨
                            hsame row sourceExport ∨ hsame row normal ∨
                              hsame row continuation ∨ hsame row siblingRead ∨
                                hsame row terminalRead ∨ hsame row downstream)
                        (fun row : BHist =>
                          (hsame row sourceExport ∨ hsame row siblingRead ∨
                            hsame row downstream) ∧
                            (PkgSig bundle sourceExport pkg ∨
                              PkgSig bundle siblingRead pkg ∨
                                PkgSig bundle downstream pkg))
                        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet typedFuelSourceRead sourceReadNameSourceExport
    normalContinuationSiblingRead typedFuelTerminalRead terminalReadContinuationDownstream
    sourceExportPkg siblingReadPkg downstreamPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, _provenancePkg⟩ :=
    packet
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelSourceRead
  have sourceExportUnary : UnaryHistory sourceExport :=
    unary_cont_closed sourceReadUnary nameUnary sourceReadNameSourceExport
  have siblingReadUnary : UnaryHistory siblingRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationSiblingRead
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminalRead
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed terminalReadUnary continuationUnary terminalReadContinuationDownstream
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro sourceExport
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
          | inr rest =>
              cases rest with
              | inl sameSibling =>
                  exact Or.inr
                    (Or.inl (hsame_trans (hsame_symm sameRows) sameSibling))
              | inr sameDownstream =>
                  exact Or.inr
                    (Or.inr (hsame_trans (hsame_symm sameRows) sameDownstream))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameSource =>
          exact Or.inr (Or.inr (Or.inr (Or.inl sameSource)))
      | inr rest =>
          cases rest with
          | inl sameSibling =>
              exact Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr (Or.inl sameSibling))))))
          | inr sameDownstream =>
              exact Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr sameDownstream)))))))
    ledger_sound := by
      intro _row source
      constructor
      · exact source.left
      · cases source.left with
        | inl _sameSource =>
            exact Or.inl sourceExportPkg
        | inr rest =>
            cases rest with
            | inl _sameSibling =>
                exact Or.inr (Or.inl siblingReadPkg)
            | inr _sameDownstream =>
                exact Or.inr (Or.inr downstreamPkg)
  }

end BEDC.Derived.ZnormalUp
