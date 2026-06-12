import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatedCauchyRepresentationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LocatedCauchyRepresentationCarrier [AskSetup] [PackageSetup]
    (decoder locatedEvidence comparisonWindow streamWindow regularReadback dyadicTolerance
      representedExposure realSeal transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory decoder ∧ UnaryHistory locatedEvidence ∧ UnaryHistory comparisonWindow ∧
    UnaryHistory streamWindow ∧ UnaryHistory regularReadback ∧
      UnaryHistory dyadicTolerance ∧ UnaryHistory representedExposure ∧
        UnaryHistory realSeal ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
          UnaryHistory provenance ∧ UnaryHistory localName ∧
            Cont decoder streamWindow regularReadback ∧
              Cont locatedEvidence regularReadback dyadicTolerance ∧
                Cont comparisonWindow dyadicTolerance representedExposure ∧
                  Cont representedExposure realSeal replay ∧
                    Cont transport replay provenance ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle localName pkg

theorem LocatedCauchyRepresentationNamecertObligations [AskSetup] [PackageSetup]
    {decoder locatedEvidence comparisonWindow streamWindow regularReadback dyadicTolerance
      representedExposure realSeal transport replay provenance localName locatedRead readbackRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCauchyRepresentationCarrier decoder locatedEvidence comparisonWindow streamWindow
        regularReadback dyadicTolerance representedExposure realSeal transport replay provenance
        localName bundle pkg →
      Cont decoder locatedEvidence locatedRead →
        Cont locatedRead dyadicTolerance readbackRead →
          Cont readbackRead realSeal publicRead →
            PkgSig bundle publicRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row decoder ∨ hsame row locatedEvidence ∨
                      hsame row comparisonWindow ∨ hsame row streamWindow ∨
                        hsame row regularReadback ∨ hsame row dyadicTolerance ∨
                          hsame row representedExposure ∨ hsame row realSeal ∨
                            hsame row publicRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont decoder locatedEvidence locatedRead ∧
                      Cont locatedRead dyadicTolerance readbackRead ∧
                        Cont readbackRead realSeal publicRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg)
                  hsame ∧
                UnaryHistory locatedRead ∧ UnaryHistory readbackRead ∧
                  UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: LocatedCauchyRepresentationCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier decoderLocated locatedDyadicReadback readbackSealPublic publicPkg
  obtain ⟨decoderUnary, locatedUnary, _comparisonUnary, _streamUnary, _readbackUnary,
    dyadicUnary, _representedUnary, realSealUnary, _transportUnary, _replayUnary,
    provenanceUnary, _localUnary, _decoderStreamReadback, _locatedReadbackDyadic,
    _comparisonDyadicRepresented, _representedSealReplay, _transportReplayProvenance,
    provenancePkg, _localPkg⟩ := carrier
  have locatedReadUnary : UnaryHistory locatedRead :=
    unary_cont_closed decoderUnary locatedUnary decoderLocated
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed locatedReadUnary dyadicUnary locatedDyadicReadback
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed readbackReadUnary realSealUnary readbackSealPublic
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row decoder ∨ hsame row locatedEvidence ∨ hsame row comparisonWindow ∨
              hsame row streamWindow ∨ hsame row regularReadback ∨
                hsame row dyadicTolerance ∨ hsame row representedExposure ∨
                  hsame row realSeal ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont decoder locatedEvidence locatedRead ∧
              Cont locatedRead dyadicTolerance readbackRead ∧
                Cont readbackRead realSeal publicRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicReadUnary⟩
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
      exact
        ⟨source.right, decoderLocated, locatedDyadicReadback, readbackSealPublic,
          provenancePkg, publicPkg⟩
  }
  exact ⟨cert, locatedReadUnary, readbackReadUnary, publicReadUnary⟩

end BEDC.Derived.LocatedCauchyRepresentationUp
