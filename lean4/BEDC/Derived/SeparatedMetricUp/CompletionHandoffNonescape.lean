import BEDC.Derived.SeparatedMetricUp.TasteGate

namespace BEDC.Derived.SeparatedMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SeparatedMetricPacket_completion_handoff_nonescape [AskSetup] [PackageSetup]
    {metric apartness zeroDistance limitWitness completionRoute transport provenance nameCert
      endpoint completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SeparatedMetricPacket metric apartness zeroDistance limitWitness completionRoute transport
        provenance nameCert endpoint bundle pkg →
      Cont endpoint nameCert completionRead →
        PkgSig bundle completionRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row metric ∨ hsame row limitWitness ∨ hsame row completionRoute ∨
                  hsame row zeroDistance ∨ hsame row endpoint ∨ hsame row completionRead)
              (fun row : BHist => UnaryHistory row ∧ PkgSig bundle completionRead pkg)
              hsame ∧
            UnaryHistory completionRead ∧ PkgSig bundle nameCert pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro packet endpointNameCompletion completionReadPkg
  obtain ⟨metricUnary, _apartnessUnary, zeroDistanceUnary, limitWitnessUnary,
    completionRouteUnary, _transportUnary, _provenanceUnary, nameCertUnary,
    endpointUnary, _apartnessZeroLimit, _limitCompletionTransport, _transportEndpoint,
    nameCertPkg⟩ := packet
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed endpointUnary nameCertUnary endpointNameCompletion
  have sourceCompletionRead :
      (fun row : BHist => hsame row completionRead ∧ UnaryHistory row) completionRead := by
    exact ⟨hsame_refl completionRead, completionReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric ∨ hsame row limitWitness ∨ hsame row completionRoute ∨
              hsame row zeroDistance ∨ hsame row endpoint ∨ hsame row completionRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle completionRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro completionRead sourceCompletionRead
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, completionReadPkg⟩
  }
  exact ⟨cert, completionReadUnary, nameCertPkg⟩

end BEDC.Derived.SeparatedMetricUp
