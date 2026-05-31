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

theorem MetaCICCriticalPathPhaseRealDependencyDiamond [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal dependencyDiamond : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg ->
      Cont handoff continuation dependencyDiamond ->
        PkgSig bundle dependencyDiamond pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row dependencyDiamond ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                  hsame row realSeal ∨ hsame row dependencyDiamond)
              (fun row : BHist =>
                hsame row dependencyDiamond ∧ PkgSig bundle dependencyDiamond pkg ∧
                  Cont handoff continuation dependencyDiamond)
              hsame ∧
            UnaryHistory dependencyDiamond := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro ledger handoffContinuationDiamond dependencyDiamondPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, _realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, _realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, handoffUnary, continuationUnary, _provenanceUnary, _localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have dependencyDiamondUnary : UnaryHistory dependencyDiamond :=
    unary_cont_closed handoffUnary continuationUnary handoffContinuationDiamond
  have sourceDiamond :
      (fun row : BHist => hsame row dependencyDiamond ∧ UnaryHistory row)
        dependencyDiamond := by
    exact ⟨hsame_refl dependencyDiamond, dependencyDiamondUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row dependencyDiamond ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row dependencyDiamond)
          (fun row : BHist =>
            hsame row dependencyDiamond ∧ PkgSig bundle dependencyDiamond pkg ∧
              Cont handoff continuation dependencyDiamond)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro dependencyDiamond sourceDiamond
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
      exact ⟨source.left, dependencyDiamondPkg, handoffContinuationDiamond⟩
  }
  exact ⟨cert, dependencyDiamondUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
