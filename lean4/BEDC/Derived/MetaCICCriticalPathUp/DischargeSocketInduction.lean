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

theorem MetaCICCriticalPathDischargeSocketInduction [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont discharge realSeal socketRead →
        PkgSig bundle socketRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row socketRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row obstruction ∨ hsame row discharge ∨ hsame row realSeal ∨
                  hsame row socketRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle socketRead pkg ∧
                  Cont discharge realSeal socketRead)
              hsame ∧
            UnaryHistory socketRead ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro ledger dischargeRealSealSocket socketReadPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    dischargeUnary, _handoffUnary, _continuationUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed dischargeUnary realSealUnary dischargeRealSealSocket
  have sourceSocketRead :
      (fun row : BHist => hsame row socketRead ∧ UnaryHistory row) socketRead := by
    exact ⟨hsame_refl socketRead, socketReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row socketRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row obstruction ∨ hsame row discharge ∨ hsame row realSeal ∨
              hsame row socketRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle socketRead pkg ∧
              Cont discharge realSeal socketRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro socketRead sourceSocketRead
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, socketReadPkg, dischargeRealSealSocket⟩
  }
  exact ⟨cert, socketReadUnary, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
