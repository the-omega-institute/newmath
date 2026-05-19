import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacketFiniteNormalwordClassifierCompatibility [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name normalRead
      classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont normal continuation normalRead →
        Cont normalRead routes classifierRead →
          PkgSig bundle classifierRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  Cont normal continuation normalRead ∧ Cont normalRead routes row ∧
                    PkgSig bundle classifierRead pkg)
                (fun row : BHist => UnaryHistory row ∧ PkgSig bundle classifierRead pkg)
                hsame ∧
              UnaryHistory normalRead ∧ UnaryHistory classifierRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro packet normalContinuationRead normalReadRoutesClassifier classifierPkg
  obtain ⟨_typedUnary, _fuelUnary, _terminalUnary, normalUnary, continuationUnary,
    _transportsUnary, routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, _provenancePkg⟩ :=
    packet
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationRead
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed normalReadUnary routesUnary normalReadRoutesClassifier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            Cont normal continuation normalRead ∧ Cont normalRead routes row ∧
              PkgSig bundle classifierRead pkg)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle classifierRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro classifierRead
          (And.intro (hsame_refl classifierRead) classifierUnary)
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
        intro _row _row' sameRows sourceData
        exact
          And.intro
            (hsame_trans (hsame_symm sameRows) sourceData.left)
            (unary_transport sourceData.right sameRows)
    }
    pattern_sound := by
      intro _row sourceData
      exact
        ⟨normalContinuationRead,
          cont_result_hsame_transport normalReadRoutesClassifier
            (hsame_symm sourceData.left),
          classifierPkg⟩
    ledger_sound := by
      intro _row sourceData
      exact And.intro sourceData.right classifierPkg
  }
  exact ⟨cert, normalReadUnary, classifierUnary⟩

end BEDC.Derived.ZnormalUp
