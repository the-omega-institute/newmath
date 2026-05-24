import BEDC.Derived.LipschitzMapUp.CommonBoundCompletionRoute

namespace BEDC.Derived.LipschitzMapUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LipschitzMapCarrier_scoped_modulus_route [AskSetup] [PackageSetup]
    {source target bound graph modulus transports routes provenance localCert consumer realSeal
      completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LipschitzMapCarrier source target bound graph modulus transports routes provenance localCert
        bundle pkg →
      Cont provenance localCert consumer →
        Cont modulus routes realSeal →
          Cont realSeal consumer completionRead →
            PkgSig bundle completionRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row source ∨ hsame row target ∨ hsame row bound ∨
                      hsame row graph ∨ hsame row modulus ∨ hsame row consumer ∨
                        hsame row realSeal ∨ hsame row completionRead)
                  (fun row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle completionRead pkg ∧
                      hsame row completionRead)
                  hsame ∧
                UnaryHistory modulus ∧ UnaryHistory consumer ∧ UnaryHistory realSeal ∧
                  UnaryHistory completionRead ∧ Cont graph bound modulus ∧
                    Cont modulus routes provenance ∧ Cont provenance localCert consumer ∧
                      Cont modulus routes realSeal ∧ Cont realSeal consumer completionRead ∧
                        PkgSig bundle provenance pkg ∧
                          PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro carrier provenanceLocalCertConsumer modulusRoutesRealSeal realSealConsumerCompletion
    completionPkg
  have routeFacts :=
    LipschitzMapCarrier_boundary_completion_consumer_route carrier provenanceLocalCertConsumer
      modulusRoutesRealSeal realSealConsumerCompletion completionPkg
  obtain
    ⟨modulusUnary, consumerUnary, realSealUnary, completionUnary, graphBoundModulus,
      modulusRoutesProvenance, _provenanceLocalCertConsumer, _modulusRoutesRealSeal,
      _realSealConsumerCompletion, provenancePkg, _completionPkg⟩ := routeFacts
  have sourceCompletion :
      (fun row : BHist => hsame row completionRead ∧ UnaryHistory row) completionRead := by
    exact ⟨hsame_refl completionRead, completionUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row target ∨ hsame row bound ∨
              hsame row graph ∨ hsame row modulus ∨ hsame row consumer ∨
                hsame row realSeal ∨ hsame row completionRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle completionRead pkg ∧
              hsame row completionRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro completionRead sourceCompletion
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, completionPkg, source.left⟩
  }
  exact
    ⟨cert, modulusUnary, consumerUnary, realSealUnary, completionUnary, graphBoundModulus,
      modulusRoutesProvenance, provenanceLocalCertConsumer, modulusRoutesRealSeal,
      realSealConsumerCompletion, provenancePkg, completionPkg⟩

end BEDC.Derived.LipschitzMapUp
