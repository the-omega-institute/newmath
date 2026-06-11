import BEDC.Derived.MetaCICCriticalPathUp.OpenPhase
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathCandidateSNHandoffSourceExhaustion [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateRead betaRead snRead sourceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName candidateRead →
        Cont candidateRead handoff betaRead →
          Cont betaRead realSeal snRead →
            Cont snRead provenance sourceRead →
              PkgSig bundle sourceRead pkg →
                SemanticNameCert
                    (fun row : BHist =>
                      (hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                        hsame row realSeal ∨ hsame row sourceRead) ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                        hsame row realSeal ∨ hsame row candidateRead ∨
                          hsame row betaRead ∨ hsame row snRead ∨ hsame row sourceRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle sourceRead pkg ∧
                        PkgSig bundle realSeal pkg)
                    hsame ∧
                  UnaryHistory sourceRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame SemanticNameCert
  intro ledger candidateRoute betaRoute snRoute sourceRoute sourcePkg
  obtain ⟨packet, dyadicUnary, streamUnary, regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, handoffUnary, continuationUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed continuationUnary localNameUnary candidateRoute
  have betaUnary : UnaryHistory betaRead :=
    unary_cont_closed candidateUnary handoffUnary betaRoute
  have snUnary : UnaryHistory snRead :=
    unary_cont_closed betaUnary realSealUnary snRoute
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed snUnary provenanceUnary sourceRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row sourceRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row candidateRead ∨ hsame row betaRead ∨
                hsame row snRead ∨ hsame row sourceRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle sourceRead pkg ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro sourceRead
          ⟨Or.inr (Or.inr (Or.inr (Or.inr (hsame_refl sourceRead)))), sourceUnary⟩
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
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameDyadic =>
          exact Or.inl sameDyadic
      | inr rest =>
          cases rest with
          | inl sameStream =>
              exact Or.inr (Or.inl sameStream)
          | inr rest =>
              cases rest with
              | inl sameRegseq =>
                  exact Or.inr (Or.inr (Or.inl sameRegseq))
              | inr rest =>
                  cases rest with
                  | inl sameRealSeal =>
                      exact Or.inr (Or.inr (Or.inr (Or.inl sameRealSeal)))
                  | inr sameSource =>
                      exact
                        Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr (Or.inr (Or.inr sameSource))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sourcePkg, realSealPkg⟩
  }
  exact ⟨cert, sourceUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
