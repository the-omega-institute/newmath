import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathObstructionScopeSeparation [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName obstructionRead socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont normalForm obstruction obstructionRead →
        Cont obstructionRead dischargeSocket socketRead →
          PkgSig bundle socketRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row socketRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row obstruction ∨ hsame row dischargeSocket ∨ hsame row socketRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle socketRead pkg ∧
                    Cont obstructionRead dischargeSocket socketRead)
                hsame ∧
              UnaryHistory obstructionRead ∧ UnaryHistory socketRead ∧
                PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: MetaCICCriticalPathPacket BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro packet normalObstructionRead obstructionSocketRead socketPkg
  obtain ⟨_strongNormUnary, normalFormUnary, obstructionUnary, _handoffUnary,
    dischargeSocketUnary, _transportUnary, _routeUnary, _provenanceUnary, _localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have obstructionReadUnary : UnaryHistory obstructionRead :=
    unary_cont_closed normalFormUnary obstructionUnary normalObstructionRead
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed obstructionReadUnary dischargeSocketUnary obstructionSocketRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row socketRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row obstruction ∨ hsame row dischargeSocket ∨ hsame row socketRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle socketRead pkg ∧
              Cont obstructionRead dischargeSocket socketRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro socketRead ⟨hsame_refl socketRead, socketReadUnary⟩
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, socketPkg, obstructionSocketRead⟩
  }
  exact ⟨cert, obstructionReadUnary, socketReadUnary, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
