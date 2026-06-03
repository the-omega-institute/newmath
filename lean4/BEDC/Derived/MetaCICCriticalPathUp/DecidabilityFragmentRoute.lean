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

theorem MetaCICCriticalPathDecidabilityFragmentRoute [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName fragmentRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket transport
        route provenance localName bundle pkg →
      Cont handoff dischargeSocket fragmentRead →
        PkgSig bundle fragmentRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row fragmentRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
                  hsame row handoff ∨ hsame row dischargeSocket ∨ hsame row transport ∨
                    hsame row route ∨ hsame row provenance ∨ hsame row localName ∨
                      hsame row fragmentRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle fragmentRead pkg ∧
                  Cont handoff dischargeSocket fragmentRead)
              hsame ∧
            PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro packet handoffSocketFragment fragmentPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, handoffUnary,
    dischargeSocketUnary, _transportUnary, _routeUnary, _provenanceUnary, _localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have fragmentUnary : UnaryHistory fragmentRead :=
    unary_cont_closed handoffUnary dischargeSocketUnary handoffSocketFragment
  have sourceFragment :
      (fun row : BHist => hsame row fragmentRead ∧ UnaryHistory row) fragmentRead := by
    exact ⟨hsame_refl fragmentRead, fragmentUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row fragmentRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
              hsame row handoff ∨ hsame row dischargeSocket ∨ hsame row transport ∨
                hsame row route ∨ hsame row provenance ∨ hsame row localName ∨
                  hsame row fragmentRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle fragmentRead pkg ∧
              Cont handoff dischargeSocket fragmentRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro fragmentRead sourceFragment
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, fragmentPkg, handoffSocketFragment⟩
  }
  exact ⟨cert, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
