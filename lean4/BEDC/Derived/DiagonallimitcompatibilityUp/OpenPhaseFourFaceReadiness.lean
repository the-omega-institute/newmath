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

theorem DiagonalLimitCompatibilityOpenPhaseFourFaceReadiness [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      streamFace dyadicFace readbackFace sealFace readiness : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal windows streamFace ->
        Cont streamFace dyadic dyadicFace ->
          Cont dyadicFace readback readbackFace ->
            Cont readbackFace realSeal sealFace ->
              Cont sealFace cert readiness ->
                PkgSig bundle readiness pkg ->
                  SemanticNameCert
                    (fun row : BHist =>
                      DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows
                          readback realSeal transport route provenance cert bundle pkg ∧
                        hsame row readiness)
                    (fun row : BHist => hsame row readiness ∧ UnaryHistory row)
                    (fun _row : BHist =>
                      Cont diagonal windows streamFace ∧
                        Cont streamFace dyadic dyadicFace ∧
                          Cont dyadicFace readback readbackFace ∧
                            Cont readbackFace realSeal sealFace ∧
                              Cont sealFace cert readiness ∧ PkgSig bundle readiness pkg)
                    hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier diagonalWindowsStream streamDyadicFace dyadicFaceReadback
    readbackFaceRealSeal sealCertReadiness readinessPkg
  have carrierWitness := carrier
  obtain ⟨diagonalUnary, _triangleUnary, _sealUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, _provenancePkg⟩ := carrier
  have streamUnary : UnaryHistory streamFace :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsStream
  have dyadicFaceUnary : UnaryHistory dyadicFace :=
    unary_cont_closed streamUnary dyadicUnary streamDyadicFace
  have readbackFaceUnary : UnaryHistory readbackFace :=
    unary_cont_closed dyadicFaceUnary readbackUnary dyadicFaceReadback
  have sealFaceUnary : UnaryHistory sealFace :=
    unary_cont_closed readbackFaceUnary realSealUnary readbackFaceRealSeal
  have readinessUnary : UnaryHistory readiness :=
    unary_cont_closed sealFaceUnary certUnary sealCertReadiness
  exact {
    core := {
      carrier_inhabited := Exists.intro readiness (And.intro carrierWitness (hsame_refl readiness))
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
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.right, unary_transport readinessUnary (hsame_symm source.right)⟩
    ledger_sound := by
      intro _row _source
      exact
        ⟨diagonalWindowsStream, streamDyadicFace, dyadicFaceReadback, readbackFaceRealSeal,
          sealCertReadiness, readinessPkg⟩
  }

end BEDC.Derived.DiagonallimitcompatibilityUp
