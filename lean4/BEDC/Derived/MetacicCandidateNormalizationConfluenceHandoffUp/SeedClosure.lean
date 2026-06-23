import BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicCandidateNormalizationConfluenceHandoffSeedClosure [AskSetup] [PackageSetup]
    {A K N F C D B T R P L candidateRead frontierRead endpointRead seedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicCandidateNormalizationConfluenceHandoffCarrier A K N F C D B T R P L bundle pkg →
      Cont A K candidateRead →
        Cont candidateRead F frontierRead →
          Cont frontierRead N endpointRead →
            Cont endpointRead L seedRead →
              PkgSig bundle seedRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row seedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row A ∨ hsame row K ∨ hsame row N ∨ hsame row F ∨
                        hsame row C ∨ hsame row D ∨ hsame row B ∨ hsame row T ∨
                          hsame row R ∨ hsame row P ∨ hsame row L ∨ hsame row seedRead)
                    (fun _row : BHist =>
                      UnaryHistory seedRead ∧ Cont A K candidateRead ∧
                        Cont candidateRead F frontierRead ∧
                          Cont frontierRead N endpointRead ∧
                            Cont endpointRead L seedRead ∧ PkgSig bundle seedRead pkg)
                    hsame ∧
                  UnaryHistory candidateRead ∧ UnaryHistory frontierRead ∧
                    UnaryHistory endpointRead ∧ UnaryHistory seedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrier auditCandidateRoute candidateFrontierRoute frontierEndpointRoute
    endpointLocalRoute seedPkg
  have auditUnary : UnaryHistory A := carrier.left
  have candidateUnary : UnaryHistory K := carrier.right.left
  have endpointUnary : UnaryHistory N := carrier.right.right.left
  have frontierUnary : UnaryHistory F := carrier.right.right.right.left
  have localNameUnary : UnaryHistory L :=
    carrier.right.right.right.right.right.right.right.right.right.right.left
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed auditUnary candidateUnary auditCandidateRoute
  have frontierReadUnary : UnaryHistory frontierRead :=
    unary_cont_closed candidateReadUnary frontierUnary candidateFrontierRoute
  have endpointReadUnary : UnaryHistory endpointRead :=
    unary_cont_closed frontierReadUnary endpointUnary frontierEndpointRoute
  have seedReadUnary : UnaryHistory seedRead :=
    unary_cont_closed endpointReadUnary localNameUnary endpointLocalRoute
  have sourceAtSeed :
      (fun row : BHist => hsame row seedRead ∧ UnaryHistory row) seedRead :=
    ⟨hsame_refl seedRead, seedReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row seedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row K ∨ hsame row N ∨ hsame row F ∨ hsame row C ∨
              hsame row D ∨ hsame row B ∨ hsame row T ∨ hsame row R ∨ hsame row P ∨
                hsame row L ∨ hsame row seedRead)
          (fun _row : BHist =>
            UnaryHistory seedRead ∧ Cont A K candidateRead ∧
              Cont candidateRead F frontierRead ∧ Cont frontierRead N endpointRead ∧
                Cont endpointRead L seedRead ∧ PkgSig bundle seedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro seedRead sourceAtSeed
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
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row _source
      exact
        ⟨seedReadUnary, auditCandidateRoute, candidateFrontierRoute, frontierEndpointRoute,
          endpointLocalRoute, seedPkg⟩
  }
  exact ⟨cert, candidateReadUnary, frontierReadUnary, endpointReadUnary, seedReadUnary⟩

end BEDC.Derived
