import BEDC.Derived.MetaCICCriticalPathUp.OpenPhase

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathOpenPhaseSourceLedgerDischargeBudget [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal sourceRead dischargeRead endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg ->
      (hsame sourceRead dyadic ∨ hsame sourceRead stream ∨ hsame sourceRead regseq ∨
          hsame sourceRead realSeal) ->
        Cont sourceRead discharge dischargeRead ->
          Cont dischargeRead handoff endpoint ->
            PkgSig bundle endpoint pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                      hsame row realSeal ∨ hsame row obstruction ∨ hsame row handoff ∨
                        hsame row discharge ∨ hsame row endpoint)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont sourceRead discharge dischargeRead ∧
                      Cont dischargeRead handoff endpoint ∧ PkgSig bundle endpoint pkg ∧
                        PkgSig bundle realSeal pkg)
                  hsame ∧
                UnaryHistory sourceRead ∧ UnaryHistory dischargeRead ∧
                  UnaryHistory endpoint := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro ledger sourceCase sourceDischargeRead dischargeHandoffEndpoint endpointPkg
  obtain ⟨packet, dyadicUnary, streamUnary, regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    dischargeUnary, handoffUnary, _continuationUnary, _provenanceUnary, _localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have sourceReadUnary : UnaryHistory sourceRead := by
    cases sourceCase with
    | inl sourceDyadic =>
        exact unary_transport dyadicUnary (hsame_symm sourceDyadic)
    | inr rest =>
        cases rest with
        | inl sourceStream =>
            exact unary_transport streamUnary (hsame_symm sourceStream)
        | inr rest =>
            cases rest with
            | inl sourceRegseq =>
                exact unary_transport regseqUnary (hsame_symm sourceRegseq)
            | inr sourceRealSeal =>
                exact unary_transport realSealUnary (hsame_symm sourceRealSeal)
  have dischargeReadUnary : UnaryHistory dischargeRead :=
    unary_cont_closed sourceReadUnary dischargeUnary sourceDischargeRead
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed dischargeReadUnary handoffUnary dischargeHandoffEndpoint
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row obstruction ∨ hsame row handoff ∨
                hsame row discharge ∨ hsame row endpoint)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont sourceRead discharge dischargeRead ∧
              Cont dischargeRead handoff endpoint ∧ PkgSig bundle endpoint pkg ∧
                PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint ⟨hsame_refl endpoint, endpointUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sourceDischargeRead, dischargeHandoffEndpoint, endpointPkg,
          realSealPkg⟩
  }
  exact ⟨cert, sourceReadUnary, dischargeReadUnary, endpointUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
