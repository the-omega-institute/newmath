import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ApproximationTowerResidueUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ApproximationTowerResidueCarrier [AskSetup] [PackageSetup]
    (source tower classifier ledger failure recovery descent transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory source ∧ UnaryHistory tower ∧ UnaryHistory classifier ∧
    UnaryHistory ledger ∧ UnaryHistory failure ∧ UnaryHistory recovery ∧
      UnaryHistory descent ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory localName ∧
          Cont source tower classifier ∧ Cont classifier ledger failure ∧
            Cont failure recovery descent ∧ Cont descent transport replay ∧
              Cont replay provenance localName ∧ PkgSig bundle localName pkg

theorem ApproximationTowerResidue_recovery_route_determinacy [AskSetup] [PackageSetup]
    {source tower classifier ledger failure recovery descent transport replay provenance
      localName recoveryRead descentRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApproximationTowerResidueCarrier source tower classifier ledger failure recovery descent
        transport replay provenance localName bundle pkg ->
      Cont recovery descent recoveryRead ->
        Cont recoveryRead transport descentRead ->
          PkgSig bundle recoveryRead pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  ApproximationTowerResidueCarrier source tower classifier ledger failure
                      recovery descent transport replay provenance localName bundle pkg ∧
                    (hsame row recoveryRead ∨ hsame row descentRead))
                (fun _row : BHist =>
                  Cont recovery descent recoveryRead ∧ Cont recoveryRead transport descentRead)
                (fun row : BHist => UnaryHistory row ∧ PkgSig bundle recoveryRead pkg)
                hsame ∧
              UnaryHistory recoveryRead ∧ UnaryHistory descentRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier recoveryRoute descentRoute recoveryPkg
  have carrierWitness := carrier
  obtain ⟨_sourceUnary, _towerUnary, _classifierUnary, _ledgerUnary, _failureUnary,
    recoveryUnary, descentUnary, transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _sourceTowerClassifier, _classifierLedgerFailure,
    _failureRecoveryDescent, _descentTransportReplay, _replayProvenanceLocalName,
    _localPkg⟩ := carrier
  have recoveryReadUnary : UnaryHistory recoveryRead :=
    unary_cont_closed recoveryUnary descentUnary recoveryRoute
  have descentReadUnary : UnaryHistory descentRead :=
    unary_cont_closed recoveryReadUnary transportUnary descentRoute
  have carrierInhabited :
      Exists
        (fun row : BHist =>
          ApproximationTowerResidueCarrier source tower classifier ledger failure recovery
              descent transport replay provenance localName bundle pkg ∧
            (hsame row recoveryRead ∨ hsame row descentRead)) :=
    Exists.intro recoveryRead ⟨carrierWitness, Or.inl (hsame_refl recoveryRead)⟩
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          ApproximationTowerResidueCarrier source tower classifier ledger failure recovery
              descent transport replay provenance localName bundle pkg ∧
            (hsame row recoveryRead ∨ hsame row descentRead))
        (fun _row : BHist =>
          Cont recovery descent recoveryRead ∧ Cont recoveryRead transport descentRead)
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle recoveryRead pkg)
        hsame := {
    core := {
      carrier_inhabited := carrierInhabited
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
        intro row other sameRows source
        cases source with
        | intro carrierSource sourceRead =>
            refine ⟨carrierSource, ?_⟩
            cases sourceRead with
            | inl sameRecovery =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) sameRecovery)
            | inr sameDescent =>
                exact Or.inr (hsame_trans (hsame_symm sameRows) sameDescent)
    }
    pattern_sound := by
      intro _row _source
      exact ⟨recoveryRoute, descentRoute⟩
    ledger_sound := by
      intro row source
      cases source with
      | intro _carrierSource sourceRead =>
          cases sourceRead with
          | inl sameRecovery =>
              exact ⟨unary_transport recoveryReadUnary (hsame_symm sameRecovery), recoveryPkg⟩
          | inr sameDescent =>
              exact ⟨unary_transport descentReadUnary (hsame_symm sameDescent), recoveryPkg⟩
  }
  exact ⟨cert, recoveryReadUnary, descentReadUnary⟩

end BEDC.Derived.ApproximationTowerResidueUp
