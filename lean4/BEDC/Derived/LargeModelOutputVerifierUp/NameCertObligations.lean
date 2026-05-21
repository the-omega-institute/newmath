import BEDC.Derived.LargeModelOutputVerifierUp.TasteGate

namespace BEDC.Derived.LargeModelOutputVerifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem LargeModelOutputVerifierNameCertObligations [AskSetup] [PackageSetup]
    {harness auditChannel modelTrace promptResponse inscriptionAudit verifier proofCheck
      refusal route replay provenance localName verifierProof publicRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont verifier proofCheck verifierProof ->
      Cont verifierProof refusal route ->
        Cont route replay publicRoute ->
          PkgSig bundle publicRoute pkg ->
            largeModelOutputVerifierFields
                (LargeModelOutputVerifierUp.mk harness auditChannel modelTrace promptResponse
                  inscriptionAudit verifier proofCheck refusal route replay provenance localName) =
              [harness, auditChannel, modelTrace, promptResponse, inscriptionAudit, verifier,
                proofCheck, refusal, route, replay, provenance, localName] ∧
              SemanticNameCert
                (fun row : BHist => hsame row publicRoute ∧ Cont route replay publicRoute)
                (fun row : BHist =>
                  hsame row publicRoute ∧ Cont verifier proofCheck verifierProof ∧
                    Cont verifierProof refusal route)
                (fun row : BHist => hsame row publicRoute ∧ PkgSig bundle publicRoute pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro verifierRoute refusalRoute publicRouteCont packageRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row publicRoute ∧ Cont route replay publicRoute)
        (fun row : BHist =>
          hsame row publicRoute ∧ Cont verifier proofCheck verifierProof ∧
            Cont verifierProof refusal route)
        (fun row : BHist => hsame row publicRoute ∧ PkgSig bundle publicRoute pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRoute ⟨hsame_refl publicRoute, publicRouteCont⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, verifierRoute, refusalRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, packageRoute⟩
  }
  exact ⟨rfl, cert⟩

end BEDC.Derived.LargeModelOutputVerifierUp
