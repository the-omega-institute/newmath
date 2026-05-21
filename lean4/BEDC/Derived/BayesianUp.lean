import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BayesianUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BayesianPosteriorPacket [AskSetup] [PackageSetup]
    (prior likelihood evidence posterior update normalisation provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory prior ∧ UnaryHistory likelihood ∧ UnaryHistory evidence ∧
    UnaryHistory posterior ∧ UnaryHistory provenance ∧ Cont prior likelihood update ∧
      Cont update evidence posterior ∧ Cont evidence posterior normalisation ∧
        Cont provenance normalisation endpoint ∧ PkgSig bundle endpoint pkg

theorem BayesianPosteriorPacket_source_obligation [AskSetup] [PackageSetup]
    {prior likelihood evidence posterior update normalisation provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BayesianPosteriorPacket prior likelihood evidence posterior update normalisation provenance
        endpoint bundle pkg ->
      UnaryHistory prior ∧ UnaryHistory likelihood ∧ UnaryHistory evidence ∧
        UnaryHistory posterior ∧ Cont prior likelihood update ∧ Cont update evidence posterior ∧
          Cont evidence posterior normalisation ∧ hsame endpoint (append provenance normalisation) ∧
            PkgSig bundle endpoint pkg := by
  intro packet
  obtain ⟨priorUnary, likelihoodUnary, evidenceUnary, posteriorUnary, _provenanceUnary,
    updateRow, posteriorRow, normalisationRow, endpointRow, pkgRow⟩ := packet
  exact
    ⟨priorUnary, likelihoodUnary, evidenceUnary, posteriorUnary, updateRow, posteriorRow,
      normalisationRow, endpointRow, pkgRow⟩

theorem BayesianPosteriorPacket_non_escape_boundary [AskSetup] [PackageSetup]
    {prior likelihood evidence posterior update normalisation provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BayesianPosteriorPacket prior likelihood evidence posterior update normalisation provenance
        endpoint bundle pkg ->
      UnaryHistory provenance ->
        UnaryHistory endpoint ∧ hsame endpoint (append provenance normalisation) ∧
          PkgSig bundle endpoint pkg := by
  intro packet provenanceUnary
  have normalisationUnary : UnaryHistory normalisation :=
    unary_cont_closed packet.right.right.left packet.right.right.right.left
      packet.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary normalisationUnary
      packet.right.right.right.right.right.right.right.right.left
  exact And.intro endpointUnary
    (And.intro packet.right.right.right.right.right.right.right.right.left
      packet.right.right.right.right.right.right.right.right.right)

def BayesianPosteriorSurface [AskSetup] [PackageSetup]
    (prior likelihood evidence posterior normalizer classifier provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory prior ∧ UnaryHistory likelihood ∧ UnaryHistory evidence ∧
    Cont prior likelihood normalizer ∧ Cont normalizer evidence posterior ∧
      hsame classifier posterior ∧ PkgSig bundle provenance pkg

theorem BayesianPosteriorSurface_source_obligation [AskSetup] [PackageSetup]
    {prior likelihood evidence posterior normalizer classifier provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BayesianPosteriorSurface prior likelihood evidence posterior normalizer classifier
      provenance bundle pkg ->
        UnaryHistory prior ∧ UnaryHistory likelihood ∧ UnaryHistory evidence ∧
          UnaryHistory normalizer ∧ UnaryHistory posterior ∧
            Cont prior likelihood normalizer ∧ Cont normalizer evidence posterior ∧
              hsame classifier posterior ∧ PkgSig bundle provenance pkg := by
  intro surface
  have normalizerUnary : UnaryHistory normalizer :=
    unary_cont_closed surface.left surface.right.left surface.right.right.right.left
  have posteriorUnary : UnaryHistory posterior :=
    unary_cont_closed normalizerUnary surface.right.right.left
      surface.right.right.right.right.left
  exact And.intro surface.left
    (And.intro surface.right.left
      (And.intro surface.right.right.left
        (And.intro normalizerUnary
          (And.intro posteriorUnary
            (And.intro surface.right.right.right.left
              (And.intro surface.right.right.right.right.left
                (And.intro surface.right.right.right.right.right.left
                  surface.right.right.right.right.right.right)))))))

theorem BayesianPosteriorSurface_update_ledger_exactness [AskSetup] [PackageSetup]
    {prior likelihood evidence posterior normalizer classifier provenance ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BayesianPosteriorSurface prior likelihood evidence posterior normalizer classifier
      provenance bundle pkg ->
        Cont posterior provenance ledger -> UnaryHistory provenance ->
          UnaryHistory ledger ∧ hsame ledger (append posterior provenance) ∧
            hsame classifier posterior ∧ PkgSig bundle provenance pkg := by
  intro surface ledgerCont provenanceUnary
  have sourceRows :=
    BayesianPosteriorSurface_source_obligation surface
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed sourceRows.right.right.right.right.left provenanceUnary ledgerCont
  exact And.intro ledgerUnary
    (And.intro ledgerCont
      (And.intro sourceRows.right.right.right.right.right.right.right.left
        sourceRows.right.right.right.right.right.right.right.right))

theorem BayesianPosteriorPacket_classifier_transport [AskSetup] [PackageSetup]
    {prior likelihood evidence posterior update normalisation provenance endpoint prior'
      likelihood' evidence' posterior' update' normalisation' provenance' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BayesianPosteriorPacket prior likelihood evidence posterior update normalisation provenance
        endpoint bundle pkg ->
      hsame prior prior' -> hsame likelihood likelihood' -> hsame evidence evidence' ->
        hsame posterior posterior' -> hsame provenance provenance' ->
          Cont prior' likelihood' update' -> Cont update' evidence' posterior' ->
            Cont evidence' posterior' normalisation' ->
              Cont provenance' normalisation' endpoint' ->
                PkgSig bundle endpoint' pkg ->
                  BayesianPosteriorPacket prior' likelihood' evidence' posterior' update'
                    normalisation' provenance' endpoint' bundle pkg ∧ hsame endpoint endpoint' := by
  intro packet samePrior sameLikelihood sameEvidence samePosterior sameProvenance
  intro priorLikelihoodUpdate updateEvidencePosterior evidencePosteriorNormalisation
  intro provenanceNormalisationEndpoint endpointPkg
  have normalisationSame : hsame normalisation normalisation' :=
    cont_respects_hsame sameEvidence samePosterior
      packet.right.right.right.right.right.right.right.left evidencePosteriorNormalisation
  have endpointSame : hsame endpoint endpoint' :=
    cont_respects_hsame sameProvenance normalisationSame
      packet.right.right.right.right.right.right.right.right.left provenanceNormalisationEndpoint
  exact And.intro
    (And.intro (unary_transport packet.left samePrior)
      (And.intro (unary_transport packet.right.left sameLikelihood)
        (And.intro (unary_transport packet.right.right.left sameEvidence)
          (And.intro (unary_transport packet.right.right.right.left samePosterior)
            (And.intro (unary_transport packet.right.right.right.right.left sameProvenance)
              (And.intro priorLikelihoodUpdate
                (And.intro updateEvidencePosterior
                  (And.intro evidencePosteriorNormalisation
                    (And.intro provenanceNormalisationEndpoint endpointPkg)))))))))
    endpointSame

theorem BayesianPosteriorPacket_carrier_introduction [AskSetup] [PackageSetup]
    {prior likelihood evidence posterior update normalisation provenance endpoint publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BayesianPosteriorPacket prior likelihood evidence posterior update normalisation provenance
        endpoint bundle pkg ->
      Cont endpoint provenance publicRead ->
        PkgSig bundle publicRead pkg ->
          UnaryHistory prior ∧ UnaryHistory likelihood ∧ UnaryHistory evidence ∧
            UnaryHistory posterior ∧ UnaryHistory publicRead ∧ Cont prior likelihood update ∧
              Cont update evidence posterior ∧ Cont evidence posterior normalisation ∧
                Cont endpoint provenance publicRead ∧
                  hsame endpoint (append provenance normalisation) ∧
                    PkgSig bundle endpoint pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame
  intro packet endpointProvenanceRead publicReadPkg
  obtain ⟨priorUnary, likelihoodUnary, evidenceUnary, posteriorUnary, provenanceUnary,
    updateRow, posteriorRow, normalisationRow, endpointRow, endpointPkg⟩ := packet
  have normalisationUnary : UnaryHistory normalisation :=
    unary_cont_closed evidenceUnary posteriorUnary normalisationRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary normalisationUnary endpointRow
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed endpointUnary provenanceUnary endpointProvenanceRead
  exact
    ⟨priorUnary, likelihoodUnary, evidenceUnary, posteriorUnary, publicReadUnary, updateRow,
      posteriorRow, normalisationRow, endpointProvenanceRead, endpointRow, endpointPkg,
      publicReadPkg⟩

theorem BayesianPosteriorPacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {prior likelihood evidence posterior update normalisation provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BayesianPosteriorPacket prior likelihood evidence posterior update normalisation provenance
        endpoint bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          BayesianPosteriorPacket prior likelihood evidence posterior update normalisation provenance
            endpoint bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          UnaryHistory posterior ∧ Cont update evidence posterior ∧ hsame row endpoint)
        (fun row : BHist =>
          Cont evidence posterior normalisation ∧ Cont provenance normalisation endpoint ∧
            PkgSig bundle endpoint pkg ∧ hsame row endpoint)
        hsame := by
  intro packet
  exact {
    core := {
      carrier_inhabited := Exists.intro endpoint (And.intro packet (hsame_refl endpoint))
      equiv_refl := by
        intro _row _rowCarrier
        exact hsame_refl _
      equiv_symm := by
        intro _left _right sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _left _right sameRows sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm sameRows) sourceRow.right)
    }
    pattern_sound := by
      intro _row sourceRow
      obtain ⟨_priorUnary, _likelihoodUnary, _evidenceUnary, posteriorUnary,
        _provenanceUnary, _updateRow, posteriorRow, _normalisationRow, _endpointRow,
        _pkgRow⟩ := sourceRow.left
      exact ⟨posteriorUnary, posteriorRow, sourceRow.right⟩
    ledger_sound := by
      intro _row sourceRow
      obtain ⟨_priorUnary, _likelihoodUnary, _evidenceUnary, _posteriorUnary,
        _provenanceUnary, _updateRow, _posteriorRow, normalisationRow, endpointRow,
        pkgRow⟩ := sourceRow.left
      exact ⟨normalisationRow, endpointRow, pkgRow, sourceRow.right⟩
  }

end BEDC.Derived.BayesianUp
