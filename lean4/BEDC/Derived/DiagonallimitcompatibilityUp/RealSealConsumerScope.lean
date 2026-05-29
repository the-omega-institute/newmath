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

theorem DiagonalLimitCompatibilityRealSealConsumerScope [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      sealConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont readback realSeal sealConsumer →
        PkgSig bundle sealConsumer pkg →
          SemanticNameCert
              (fun row : BHist => hsame row sealConsumer ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row diagonal ∨ hsame row triangle ∨ hsame row dyadic ∨
                  hsame row windows ∨ hsame row readback ∨ hsame row realSeal ∨
                    hsame row sealConsumer)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle sealConsumer pkg)
              hsame ∧
            UnaryHistory readback ∧ UnaryHistory realSeal ∧ UnaryHistory sealConsumer ∧
              Cont readback realSeal sealConsumer ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle sealConsumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro carrier readbackRealSealConsumer sealConsumerPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, _dyadicUnary, _windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have sealConsumerUnary : UnaryHistory sealConsumer :=
    unary_cont_closed readbackUnary realSealUnary readbackRealSealConsumer
  have sourceSealConsumer :
      (fun row : BHist => hsame row sealConsumer ∧ UnaryHistory row) sealConsumer := by
    exact ⟨hsame_refl sealConsumer, sealConsumerUnary⟩
  have certScope :
      SemanticNameCert
          (fun row : BHist => hsame row sealConsumer ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row diagonal ∨ hsame row triangle ∨ hsame row dyadic ∨
              hsame row windows ∨ hsame row readback ∨ hsame row realSeal ∨
                hsame row sealConsumer)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle sealConsumer pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealConsumer sourceSealConsumer
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, sealConsumerPkg⟩
  }
  exact
    ⟨certScope, readbackUnary, realSealUnary, sealConsumerUnary, readbackRealSealConsumer,
      provenancePkg, sealConsumerPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
