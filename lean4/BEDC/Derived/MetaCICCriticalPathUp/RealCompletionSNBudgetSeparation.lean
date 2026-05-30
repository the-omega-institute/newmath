import BEDC.Derived.MetaCICCriticalPathUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathRealCompletionSNBudgetSeparation [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont regseq realSeal handoff →
        Cont handoff obstruction socketRead →
          PkgSig bundle socketRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row socketRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                    hsame row realSeal ∨ hsame row socketRead ∨
                      Cont handoff obstruction socketRead)
                (fun row : BHist =>
                  PkgSig bundle realSeal pkg ∧ PkgSig bundle socketRead pkg ∧
                    hsame row socketRead)
                hsame ∧
              UnaryHistory socketRead ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro ledger regseqRealSealHandoff handoffObstructionSocket socketPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _ledgerRegseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _unblockUnary,
    _dischargeUnary, _handoffUnary, _continuationUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed regseqUnary realSealUnary regseqRealSealHandoff
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed handoffUnary obstructionUnary handoffObstructionSocket
  have socketWitness :
      (fun row : BHist => hsame row socketRead ∧ UnaryHistory row) socketRead := by
    exact ⟨hsame_refl socketRead, socketReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row socketRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row socketRead ∨
                Cont handoff obstruction socketRead)
          (fun row : BHist =>
            PkgSig bundle realSeal pkg ∧ PkgSig bundle socketRead pkg ∧
              hsame row socketRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro socketRead socketWitness
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨realSealPkg, socketPkg, source.left⟩
  }
  exact ⟨cert, socketReadUnary, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
