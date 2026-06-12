import BEDC.Derived.MetaCICCriticalPathUp.OpenPhase
import BEDC.FKernel.NameCert
import BEDC.MetaCIC.Normalization.Reducibility

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathCandidateSNHandoff [AskSetup] [PackageSetup]
    {A t t' : BEDC.MetaCIC.Term}
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateRead betaRead snRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      BEDC.MetaCIC.Candidate A t →
        BEDC.MetaCIC.BetaStep t t' →
          Cont continuation localName candidateRead →
            Cont candidateRead handoff betaRead →
              Cont betaRead realSeal snRead →
                PkgSig bundle snRead pkg →
                  SemanticNameCert
                      (fun row : BHist =>
                        (hsame row candidateRead ∨ hsame row betaRead ∨
                          hsame row snRead ∨ hsame row realSeal) ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row strongNorm ∨ hsame row normalForm ∨ hsame row handoff ∨
                          hsame row continuation ∨ hsame row candidateRead ∨
                            hsame row betaRead ∨ hsame row snRead ∨ hsame row realSeal)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont continuation localName candidateRead ∧
                          Cont candidateRead handoff betaRead ∧
                            Cont betaRead realSeal snRead ∧ PkgSig bundle snRead pkg)
                      hsame ∧
                    BEDC.MetaCIC.StrongNormalizable t ∧
                      BEDC.MetaCIC.Candidate A t' ∧
                        BEDC.MetaCIC.StrongNormalizable t' ∧
                          UnaryHistory candidateRead ∧ UnaryHistory betaRead ∧
                            UnaryHistory snRead := by
  -- BEDC touchpoint anchor: BEDC. BHist Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro ledger candidate betaStep candidateRoute betaRoute snRoute snPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, _realSealPkg⟩ := ledger
  obtain ⟨strongNormUnary, normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, handoffUnary, continuationUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed continuationUnary localNameUnary candidateRoute
  have betaUnary : UnaryHistory betaRead :=
    unary_cont_closed candidateUnary handoffUnary betaRoute
  have snUnary : UnaryHistory snRead :=
    unary_cont_closed betaUnary realSealUnary snRoute
  have candidateSN : BEDC.MetaCIC.StrongNormalizable t :=
    BEDC.MetaCIC.candidate_implies_sn A t candidate
  have betaCandidate : BEDC.MetaCIC.Candidate A t' :=
    BEDC.MetaCIC.candidate_closed_under_beta A t t' candidate betaStep
  have betaSN : BEDC.MetaCIC.StrongNormalizable t' :=
    BEDC.MetaCIC.candidate_implies_sn A t' betaCandidate
  have sourceSN :
      (fun row : BHist =>
        (hsame row candidateRead ∨ hsame row betaRead ∨ hsame row snRead ∨
          hsame row realSeal) ∧ UnaryHistory row) snRead := by
    exact ⟨Or.inr (Or.inr (Or.inl (hsame_refl snRead))), snUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row candidateRead ∨ hsame row betaRead ∨ hsame row snRead ∨
              hsame row realSeal) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row handoff ∨
              hsame row continuation ∨ hsame row candidateRead ∨ hsame row betaRead ∨
                hsame row snRead ∨ hsame row realSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont continuation localName candidateRead ∧
              Cont candidateRead handoff betaRead ∧ Cont betaRead realSeal snRead ∧
                PkgSig bundle snRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro snRead sourceSN
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
        constructor
        · cases source.left with
          | inl sameCandidate =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameCandidate)
          | inr rest =>
              cases rest with
              | inl sameBeta =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameBeta))
              | inr rest =>
                  cases rest with
                  | inl sameSN =>
                      exact
                        Or.inr (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameSN)))
                  | inr sameRealSeal =>
                      exact
                        Or.inr (Or.inr (Or.inr
                          (hsame_trans (hsame_symm sameRows) sameRealSeal)))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameCandidate =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameCandidate))))
      | inr rest =>
          cases rest with
          | inl sameBeta =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameBeta)))))
          | inr rest =>
              cases rest with
              | inl sameSN =>
                  exact
                    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                      (Or.inl sameSN))))))
              | inr sameRealSeal =>
                  exact
                    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                      (Or.inr sameRealSeal))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, candidateRoute, betaRoute, snRoute, snPkg⟩
  }
  exact ⟨cert, candidateSN, betaCandidate, betaSN, candidateUnary, betaUnary, snUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
