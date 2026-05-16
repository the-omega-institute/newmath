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

theorem DiagonalLimitCompatibility_formal_target_packet [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont readback realSeal endpoint ->
        PkgSig bundle endpoint pkg ->
          SemanticNameCert
            (fun row : BHist =>
              DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback
                  realSeal transport route provenance cert bundle pkg ∧
                hsame row endpoint)
            (fun row : BHist => UnaryHistory row ∧ hsame row endpoint)
            (fun _row : BHist =>
              PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg ∧
                Cont dyadic windows readback ∧ Cont readback realSeal endpoint)
            hsame := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg SemanticNameCert
  intro carrier readbackEndpoint endpointPkg
  have carrierWitness := carrier
  obtain ⟨_diagonalUnary, _triangleUnary, _sealUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed readbackUnary realSealUnary readbackEndpoint
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint (And.intro carrierWitness (hsame_refl endpoint))
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
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro row source
      exact And.intro (unary_transport endpointUnary (hsame_symm source.right)) source.right
    ledger_sound := by
      intro _row _source
      exact
        ⟨provenancePkg, endpointPkg, dyadicWindowsReadback, readbackEndpoint⟩
  }

end BEDC.Derived.DiagonallimitcompatibilityUp
