import BEDC.Derived.LocatedCauchyRepresentationUp.NameCertObligations

namespace BEDC.Derived.LocatedCauchyRepresentationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedCauchyRepresentationRealSealHandoff [AskSetup] [PackageSetup]
    {decoder locatedEvidence comparisonWindow streamWindow regularReadback dyadicTolerance
      representedExposure realSeal transport replay provenance localName sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCauchyRepresentationCarrier decoder locatedEvidence comparisonWindow streamWindow
        regularReadback dyadicTolerance representedExposure realSeal transport replay provenance
        localName bundle pkg →
      Cont representedExposure realSeal sealRead →
        PkgSig bundle sealRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row decoder ∨ hsame row locatedEvidence ∨
                  hsame row comparisonWindow ∨ hsame row streamWindow ∨
                    hsame row regularReadback ∨ hsame row dyadicTolerance ∨
                      hsame row representedExposure ∨ hsame row realSeal ∨
                        hsame row sealRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont representedExposure realSeal sealRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg)
              hsame ∧
            UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: LocatedCauchyRepresentationCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier exposureSeal sealPkg
  obtain ⟨_decoderUnary, _locatedUnary, _comparisonUnary, _streamUnary, _readbackUnary,
    _dyadicUnary, exposureUnary, realSealUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localUnary, _decoderStreamReadback, _locatedReadbackDyadic,
    _comparisonDyadicRepresented, _representedSealReplay, _transportReplayProvenance,
    provenancePkg, _localPkg⟩ := carrier
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed exposureUnary realSealUnary exposureSeal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row decoder ∨ hsame row locatedEvidence ∨ hsame row comparisonWindow ∨
              hsame row streamWindow ∨ hsame row regularReadback ∨
                hsame row dyadicTolerance ∨ hsame row representedExposure ∨
                  hsame row realSeal ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont representedExposure realSeal sealRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, exposureSeal, provenancePkg, sealPkg⟩
  }
  exact ⟨cert, sealUnary⟩

end BEDC.Derived.LocatedCauchyRepresentationUp
