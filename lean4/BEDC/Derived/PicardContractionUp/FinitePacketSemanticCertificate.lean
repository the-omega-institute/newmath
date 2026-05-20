import BEDC.Derived.PicardContractionUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.PicardContractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PicardContractionCarrier_finite_packet_semantic_certificate
    [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance
      name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport
        routes provenance name bundle pkg ->
      PkgSig bundle provenance pkg ->
        UnaryHistory provenance ∧
          SemanticNameCert
            (fun row : BHist => hsame row provenance)
            (fun row : BHist =>
              hsame row banach ∨ hsame row contraction ∨ hsame row lipschitz ∨
                hsame row iterates ∨ hsame row modulus ∨ hsame row endpoint ∨
                  hsame row transport ∨ hsame row routes ∨ hsame row provenance ∨
                    hsame row name)
            (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet provenancePkg
  obtain ⟨_banachUnary, _contractionUnary, _lipschitzUnary, _iteratesUnary, _modulusUnary,
    _endpointUnary, _transportUnary, _routesUnary, provenanceUnary, _nameUnary,
    _banachContractionLipschitz, _iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, _namePkg⟩ := packet
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row provenance)
        (fun row : BHist =>
          hsame row banach ∨ hsame row contraction ∨ hsame row lipschitz ∨
            hsame row iterates ∨ hsame row modulus ∨ hsame row endpoint ∨
              hsame row transport ∨ hsame row routes ∨ hsame row provenance ∨
                hsame row name)
        (fun row : BHist => hsame row provenance ∧ PkgSig bundle provenance pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro provenance (hsame_refl provenance)
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
        exact hsame_trans (hsame_symm sameRows) source
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr (Or.inl source))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source, provenancePkg⟩
  }
  exact ⟨provenanceUnary, cert⟩

end BEDC.Derived.PicardContractionUp
