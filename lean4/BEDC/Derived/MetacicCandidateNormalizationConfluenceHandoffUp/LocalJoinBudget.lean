import BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp.CandidateResidualJoin

namespace BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp.LocalJoinBudget

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived

theorem MetacicCandidateHandoffLocalJoinBudget [AskSetup] [PackageSetup]
    {A K N F C D B T R P L candidateRead frontierRead residualRead decidableRead blockedRead
      endpointRead localJoinRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicCandidateNormalizationConfluenceHandoffCarrier A K N F C D B T R P L bundle pkg →
      Cont A K candidateRead →
        Cont candidateRead F frontierRead →
          Cont frontierRead C residualRead →
            Cont residualRead D decidableRead →
              Cont decidableRead B blockedRead →
                Cont blockedRead N endpointRead →
                  Cont endpointRead L localJoinRead →
                    PkgSig bundle localJoinRead pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row localJoinRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row K ∨ hsame row F ∨ hsame row C ∨ hsame row D ∨
                              hsame row B ∨ hsame row N ∨ hsame row T ∨ hsame row R ∨
                                hsame row P ∨ hsame row L ∨ hsame row localJoinRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ PkgSig bundle localJoinRead pkg)
                          hsame ∧
                        UnaryHistory endpointRead ∧ UnaryHistory localJoinRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier candidateRoute frontierRoute residualRoute decidableRoute blockedRoute
    endpointRoute localJoinRoute localJoinPkg
  obtain ⟨auditUnary, candidateUnary, normalEndpointUnary, frontierUnary, confluenceUnary,
    decidabilityUnary, blockedUnary, _transportUnary, _replayUnary, _provenanceUnary,
    localNameUnary, _provenancePkg⟩ := carrier
  have candidateReadUnary : UnaryHistory candidateRead :=
    unary_cont_closed auditUnary candidateUnary candidateRoute
  have frontierReadUnary : UnaryHistory frontierRead :=
    unary_cont_closed candidateReadUnary frontierUnary frontierRoute
  have residualReadUnary : UnaryHistory residualRead :=
    unary_cont_closed frontierReadUnary confluenceUnary residualRoute
  have decidableReadUnary : UnaryHistory decidableRead :=
    unary_cont_closed residualReadUnary decidabilityUnary decidableRoute
  have blockedReadUnary : UnaryHistory blockedRead :=
    unary_cont_closed decidableReadUnary blockedUnary blockedRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed blockedReadUnary normalEndpointUnary endpointRoute
  have localJoinUnary : UnaryHistory localJoinRead :=
    unary_cont_closed endpointUnary localNameUnary localJoinRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row localJoinRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row F ∨ hsame row C ∨ hsame row D ∨ hsame row B ∨
              hsame row N ∨ hsame row T ∨ hsame row R ∨ hsame row P ∨ hsame row L ∨
                hsame row localJoinRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle localJoinRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro localJoinRead ⟨hsame_refl localJoinRead, localJoinUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr sourceRow.left)))))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, localJoinPkg⟩
  }
  exact ⟨cert, endpointUnary, localJoinUnary⟩

end BEDC.Derived.MetacicCandidateNormalizationConfluenceHandoffUp.LocalJoinBudget
