import BEDC.Derived.DiagonallimitcompatibilityUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRootL10SpineExhaustion [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      streamReg dyadicSeal sealBoundary terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont windows readback streamReg ->
        Cont dyadic streamReg dyadicSeal ->
          Cont dyadicSeal realSeal sealBoundary ->
            Cont sealBoundary cert terminal ->
              PkgSig bundle terminal pkg ->
                UnaryHistory windows ∧ UnaryHistory readback ∧ UnaryHistory dyadic ∧
                  UnaryHistory realSeal ∧ UnaryHistory cert ∧ UnaryHistory streamReg ∧
                    UnaryHistory dyadicSeal ∧ UnaryHistory sealBoundary ∧
                      UnaryHistory terminal ∧ Cont windows readback streamReg ∧
                        Cont dyadic streamReg dyadicSeal ∧
                          Cont dyadicSeal realSeal sealBoundary ∧
                            Cont sealBoundary cert terminal ∧ PkgSig bundle provenance pkg ∧
                              PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle UnaryHistory
  intro carrier windowsReadbackStream dyadicStreamSeal dyadicSealRealBoundary
    boundaryCertTerminal terminalPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have streamRegUnary : UnaryHistory streamReg :=
    unary_cont_closed windowsUnary readbackUnary windowsReadbackStream
  have dyadicSealUnary : UnaryHistory dyadicSeal :=
    unary_cont_closed dyadicUnary streamRegUnary dyadicStreamSeal
  have sealBoundaryUnary : UnaryHistory sealBoundary :=
    unary_cont_closed dyadicSealUnary realSealUnary dyadicSealRealBoundary
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed sealBoundaryUnary certUnary boundaryCertTerminal
  exact
    ⟨windowsUnary, readbackUnary, dyadicUnary, realSealUnary, certUnary, streamRegUnary,
      dyadicSealUnary, sealBoundaryUnary, terminalUnary, windowsReadbackStream,
      dyadicStreamSeal, dyadicSealRealBoundary, boundaryCertTerminal, provenancePkg,
      terminalPkg⟩

theorem DiagonalLimitCompatibilityRootL10SpineExhaustion_certificate [AskSetup]
    [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      streamRead spineRead endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont dyadic windows streamRead ->
        Cont streamRead readback spineRead ->
          Cont spineRead realSeal endpoint ->
            PkgSig bundle endpoint pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row dyadic ∨ hsame row windows ∨ hsame row streamRead ∨
                      hsame row spineRead ∨ hsame row endpoint)
                  (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
                  hsame ∧
                UnaryHistory streamRead ∧ UnaryHistory spineRead ∧ UnaryHistory endpoint ∧
                  Cont dyadic windows streamRead ∧ Cont streamRead readback spineRead ∧
                    Cont spineRead realSeal endpoint ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert UnaryHistory
  intro carrier dyadicWindowsStream streamReadReadbackSpine spineReadRealEndpoint
    endpointPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have streamReadUnary : UnaryHistory streamRead :=
    unary_cont_closed dyadicUnary windowsUnary dyadicWindowsStream
  have spineReadUnary : UnaryHistory spineRead :=
    unary_cont_closed streamReadUnary readbackUnary streamReadReadbackSpine
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed spineReadUnary realSealUnary spineReadRealEndpoint
  have certData :
      SemanticNameCert
        (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row dyadic ∨ hsame row windows ∨ hsame row streamRead ∨
            hsame row spineRead ∨ hsame row endpoint)
        (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint (And.intro (hsame_refl endpoint) endpointUnary)
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
        intro row row' sameRows source
        exact
          And.intro
            (hsame_trans (hsame_symm sameRows) source.left)
            (unary_transport source.right sameRows)
    }
    pattern_sound := by
      intro row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro row source
      exact And.intro source.left endpointPkg
  }
  exact
    ⟨certData, streamReadUnary, spineReadUnary, endpointUnary, dyadicWindowsStream,
      streamReadReadbackSpine, spineReadRealEndpoint, provenancePkg, endpointPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
