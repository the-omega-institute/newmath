import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathPacket_local_name_nonescape [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName localRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont provenance localName localRead →
        PkgSig bundle localRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row localRead ∧ UnaryHistory row ∧
                PkgSig bundle row pkg)
              (fun row : BHist =>
                hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
                  hsame row handoff ∨ hsame row dischargeSocket ∨ hsame row transport ∨
                    hsame row route ∨ hsame row provenance ∨ hsame row localName ∨
                      hsame row localRead)
              (fun row : BHist =>
                hsame row localRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle localRead pkg)
              hsame ∧
            UnaryHistory localRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro packet provenanceLocalNameRead localReadPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _handoffUnary,
    _dischargeSocketUnary, _transportUnary, _routeUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have localReadUnary : UnaryHistory localRead :=
    unary_cont_closed provenanceUnary localNameUnary provenanceLocalNameRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row localRead ∧ UnaryHistory row ∧
            PkgSig bundle row pkg)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
              hsame row handoff ∨ hsame row dischargeSocket ∨ hsame row transport ∨
                hsame row route ∨ hsame row provenance ∨ hsame row localName ∨
                  hsame row localRead)
          (fun row : BHist =>
            hsame row localRead ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro localRead ⟨hsame_refl localRead, localReadUnary, localReadPkg⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg, localReadPkg⟩
  }
  exact ⟨cert, localReadUnary, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
