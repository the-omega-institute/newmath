import BEDC.Derived.ZetaContinuationApplicationUp.TasteGate

namespace BEDC.Derived.ZetaContinuationApplicationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationApplicationCarrier_gamma_horizon_boundary [AskSetup] [PackageSetup]
    {eta functional pole zeroLedger gamma application transport replay provenance name
      gammaRead gammaBoundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationApplicationCarrier eta functional pole zeroLedger gamma application transport
        replay provenance name bundle pkg →
      Cont gamma application gammaRead →
        Cont gammaRead provenance gammaBoundary →
          PkgSig bundle gammaBoundary pkg →
            SemanticNameCert
                (fun row : BHist => hsame row gammaRead ∧ UnaryHistory row)
                (fun _row : BHist => Cont gamma application gammaRead)
                (fun row : BHist => hsame row gammaRead ∧ PkgSig bundle gammaBoundary pkg)
                hsame ∧
              UnaryHistory gamma ∧ UnaryHistory application ∧ UnaryHistory provenance ∧
                UnaryHistory gammaRead ∧ UnaryHistory gammaBoundary ∧
                  Cont gamma application gammaRead ∧ Cont gammaRead provenance gammaBoundary ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle gammaBoundary pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro carrier gammaApplicationRead gammaReadProvenanceBoundary gammaBoundaryPkg
  obtain ⟨_etaUnary, _functionalUnary, _poleUnary, _zeroLedgerUnary, gammaUnary,
    applicationUnary, _transportUnary, _replayUnary, provenanceUnary, _nameUnary,
    _transportReplayProvenance, _etaFunctionalApplication, _gammaApplicationReplay,
    provenancePkg, _namePkg⟩ := carrier
  have gammaReadUnary : UnaryHistory gammaRead :=
    unary_cont_closed gammaUnary applicationUnary gammaApplicationRead
  have gammaBoundaryUnary : UnaryHistory gammaBoundary :=
    unary_cont_closed gammaReadUnary provenanceUnary gammaReadProvenanceBoundary
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row gammaRead ∧ UnaryHistory row)
          (fun _row : BHist => Cont gamma application gammaRead)
          (fun row : BHist => hsame row gammaRead ∧ PkgSig bundle gammaBoundary pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro gammaRead
        (And.intro (hsame_refl gammaRead) gammaReadUnary)
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
        exact And.intro (hsame_trans (hsame_symm sameRows) source.left)
          (unary_transport source.right sameRows)
    }
    pattern_sound := by
      intro _row _source
      exact gammaApplicationRead
    ledger_sound := by
      intro _row source
      exact And.intro source.left gammaBoundaryPkg
  }
  exact
    ⟨cert, gammaUnary, applicationUnary, provenanceUnary, gammaReadUnary, gammaBoundaryUnary,
      gammaApplicationRead, gammaReadProvenanceBoundary, provenancePkg, gammaBoundaryPkg⟩

end BEDC.Derived.ZetaContinuationApplicationUp
