import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathPhaseRealObstructionLedgerLock [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName streamSchedule regSeqReadback realSeal socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route localName streamSchedule →
        Cont streamSchedule normalForm regSeqReadback →
          Cont regSeqReadback provenance realSeal →
            Cont handoff obstruction socketRead →
              PkgSig bundle socketRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row socketRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row obstruction ∨ hsame row dischargeSocket ∨
                        hsame row socketRead ∨ hsame row realSeal)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle socketRead pkg ∧
                        PkgSig bundle provenance pkg)
                    hsame ∧
                  UnaryHistory socketRead ∧ UnaryHistory realSeal := by
  -- BEDC touchpoint anchor: MetaCICCriticalPathPacket BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro packet routeLocalNameStream streamNormalFormReadback readbackProvenanceReal
    handoffObstructionSocket socketPkg
  obtain ⟨_strongNormUnary, normalFormUnary, obstructionUnary, handoffUnary,
    dischargeSocketUnary, _transportUnary, routeUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionDischargeSocket,
    _transportLocalName, provenancePkg⟩ := packet
  have streamUnary : UnaryHistory streamSchedule :=
    unary_cont_closed routeUnary localNameUnary routeLocalNameStream
  have regSeqUnary : UnaryHistory regSeqReadback :=
    unary_cont_closed streamUnary normalFormUnary streamNormalFormReadback
  have realUnary : UnaryHistory realSeal :=
    unary_cont_closed regSeqUnary provenanceUnary readbackProvenanceReal
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed handoffUnary obstructionUnary handoffObstructionSocket
  have sourceSocket :
      (fun row : BHist => hsame row socketRead ∧ UnaryHistory row) socketRead := by
    exact ⟨hsame_refl socketRead, socketUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row socketRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row obstruction ∨ hsame row dischargeSocket ∨ hsame row socketRead ∨
              hsame row realSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle socketRead pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro socketRead sourceSocket
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
      exact Or.inr (Or.inr (Or.inl source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, socketPkg, provenancePkg⟩
  }
  exact ⟨cert, socketUnary, realUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
