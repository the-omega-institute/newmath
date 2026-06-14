import BEDC.Derived.ClosedTermSubstitutionBoundaryUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ClosedTermSubstitutionBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundarySiblingLatticeRoute [AskSetup] [PackageSetup]
    {operation socket budget generator transport replay provenance localName endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory operation ->
      UnaryHistory socket ->
        UnaryHistory budget ->
          UnaryHistory generator ->
            UnaryHistory provenance ->
              UnaryHistory localName ->
                Cont operation socket budget ->
                  Cont budget generator transport ->
                    Cont transport replay provenance ->
                      Cont provenance localName endpoint ->
                        PkgSig bundle endpoint pkg ->
                          SemanticNameCert
                              (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row operation ∨ hsame row socket ∨ hsame row budget ∨
                                  hsame row generator ∨ hsame row endpoint)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont operation socket budget ∧
                                  Cont budget generator transport ∧
                                    Cont transport replay provenance ∧
                                      Cont provenance localName endpoint ∧
                                        PkgSig bundle endpoint pkg)
                              hsame ∧
                            UnaryHistory transport ∧ UnaryHistory replay ∧
                              UnaryHistory endpoint := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro operationUnary socketUnary budgetUnary generatorUnary provenanceUnary localNameUnary
    operationSocketBudget budgetGeneratorTransport transportReplayProvenance
    provenanceLocalEndpoint endpointPkg
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed budgetUnary generatorUnary budgetGeneratorTransport
  have replayUnary : UnaryHistory replay :=
    unary_cont_right_factor transportReplayProvenance provenanceUnary
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary localNameUnary provenanceLocalEndpoint
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row operation ∨ hsame row socket ∨ hsame row budget ∨
              hsame row generator ∨ hsame row endpoint)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont operation socket budget ∧
              Cont budget generator transport ∧ Cont transport replay provenance ∧
                Cont provenance localName endpoint ∧ PkgSig bundle endpoint pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint ⟨hsame_refl endpoint, endpointUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, operationSocketBudget, budgetGeneratorTransport,
          transportReplayProvenance, provenanceLocalEndpoint, endpointPkg⟩
  }
  exact ⟨cert, transportUnary, replayUnary, endpointUnary⟩

end BEDC.Derived.ClosedTermSubstitutionBoundaryUp
