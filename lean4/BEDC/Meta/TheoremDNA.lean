import BEDC.GroundCompiler.TheoremGenerated

namespace BEDC.Meta.TheoremDNA

open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.ChannelEncoding
open BEDC.GroundCompiler.TheoremGenerated

structure TheoremDNA
    (T : TheoremCandidateFlow) (R : GeneratedTheoremRecognizer) where
  statement : TheoremCandidateFlow
  dependencies : TheoremCandidateFlow
  proof : TheoremCandidateFlow
  certificates : TheoremCandidateFlow
  ledger : TheoremCandidateFlow
  status : TheoremCandidateFlow
  canonicalSite : TheoremCandidateFlow
  closingSeal : TheoremCandidateFlow
  statement_role :
    TheoremRoleSubflow R T statement TheoremRole.statement
  dependencies_role :
    TheoremRoleSubflow R T dependencies TheoremRole.dependencies
  proof_role :
    TheoremRoleSubflow R T proof TheoremRole.proof
  certificates_role :
    TheoremRoleSubflow R T certificates TheoremRole.certificates
  ledger_role :
    TheoremRoleSubflow R T ledger TheoremRole.ledger
  status_role :
    TheoremRoleSubflow R T status TheoremRole.status
  canonical_site_role :
    TheoremRoleSubflow R T canonicalSite TheoremRole.canonicalSite
  closing_seal_role :
    TheoremRoleSubflow R T closingSeal TheoremRole.closingSeal

structure AnchoredTheoremDNA
    (T : TheoremCandidateFlow) (R : GeneratedTheoremRecognizer) where
  dna : TheoremDNA T R
  seal_source : TheoremSourceSubflow dna.closingSeal T

structure SoundTheoremDNA (T : TheoremCandidateFlow) where
  recognizer : GeneratedTheoremRecognizer
  dna : TheoremDNA T recognizer
  proof_sound : ProofSoundTheoremRecognition recognizer T
  certificate_sound : CertificateSoundTheoremRecognition recognizer T
  ledger_sound : LedgerSoundTheoremRecognition recognizer T
  status_sound : StatusSoundTheoremRecognition recognizer T
  site_sound : SiteSoundTheoremRecognition recognizer T

theorem accepted_theorem_has_theorem_dna
    {T : TheoremCandidateFlow} :
    AcceptedTheoremFlow T -> Nonempty (SoundTheoremDNA T) := by
  intro hAccepted
  cases hAccepted with
  | intro R hSound =>
      cases hSound with
      | intro hComplete hSoundRest =>
          cases hSoundRest with
          | intro hProofSound hSoundRest =>
              cases hSoundRest with
              | intro hCertificateSound hSoundRest =>
                  cases hSoundRest with
                  | intro hLedgerSound hSoundRest =>
                      cases hSoundRest with
                      | intro hStatusSound hSiteSound =>
                          cases hComplete with
                          | intro statement hComplete =>
                              cases hComplete with
                              | intro dependencies hComplete =>
                                  cases hComplete with
                                  | intro proof hComplete =>
                                      cases hComplete with
                                      | intro certificates hComplete =>
                                          cases hComplete with
                                          | intro ledger hComplete =>
                                              cases hComplete with
                                              | intro status hComplete =>
                                                  cases hComplete with
                                                  | intro canonicalSite hComplete =>
                                                      cases hComplete with
                                                      | intro closingSeal hRoles =>
                                                          cases hRoles with
                                                          | intro hStatement hRoles =>
                                                              cases hRoles with
                                                              | intro hDependencies hRoles =>
                                                                  cases hRoles with
                                                                  | intro hProof hRoles =>
                                                                      cases hRoles with
                                                                      | intro hCertificates hRoles =>
                                                                          cases hRoles with
                                                                          | intro hLedger hRoles =>
                                                                              cases hRoles with
                                                                              | intro hStatus hRoles =>
                                                                                  cases hRoles with
                                                                                  | intro hCanonicalSite hClosingSeal =>
                                                                                      constructor
                                                                                      exact {
                                                                                        recognizer := R
                                                                                        dna := {
                                                                                          statement := statement
                                                                                          dependencies := dependencies
                                                                                          proof := proof
                                                                                          certificates := certificates
                                                                                          ledger := ledger
                                                                                          status := status
                                                                                          canonicalSite := canonicalSite
                                                                                          closingSeal := closingSeal
                                                                                          statement_role := hStatement
                                                                                          dependencies_role := hDependencies
                                                                                          proof_role := hProof
                                                                                          certificates_role := hCertificates
                                                                                          ledger_role := hLedger
                                                                                          status_role := hStatus
                                                                                          canonical_site_role := hCanonicalSite
                                                                                          closing_seal_role := hClosingSeal
                                                                                        }
                                                                                        proof_sound := hProofSound
                                                                                        certificate_sound := hCertificateSound
                                                                                        ledger_sound := hLedgerSound
                                                                                        status_sound := hStatusSound
                                                                                        site_sound := hSiteSound
                                                                                      }

theorem statement_alone_not_theorem_genome
    {T : TheoremCandidateFlow} :
    (exists R : GeneratedTheoremRecognizer,
      exists statement : TheoremCandidateFlow,
        TheoremRoleSubflow R T statement TheoremRole.statement) ->
      (forall R : GeneratedTheoremRecognizer,
        TheoremRecognitionRelation R T ->
          forall proof : TheoremCandidateFlow,
            Not (TheoremRoleSubflow R T proof TheoremRole.proof)) ->
        Not (exists R : GeneratedTheoremRecognizer, Nonempty (TheoremDNA T R)) := by
  intro _ hNoProof hGenome
  cases hGenome with
  | intro R hDna =>
      cases hDna with
      | intro dna =>
          exact hNoProof R dna.statement_role.left dna.proof dna.proof_role

theorem theorem_code_not_proof :
    exists c : List DisplayAlphabet,
      LegalTheoremCode c /\
        exists T : TheoremCandidateFlow,
          Decode c = some T /\
            (forall R : GeneratedTheoremRecognizer,
              Not (ProofSoundTheoremRecognition R T)) := by
  exact theorem_code_is_not_proof

end BEDC.Meta.TheoremDNA
