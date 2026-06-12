import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathConsistencyRefusalBoundary [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName consistencyRead refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont strongNorm normalForm consistencyRead →
        Cont consistencyRead obstruction refusalRead →
          PkgSig bundle refusalRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
                    hsame row refusalRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle refusalRead pkg ∧
                    PkgSig bundle provenance pkg)
                hsame ∧
              UnaryHistory consistencyRead ∧ UnaryHistory refusalRead ∧
                PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: MetaCICCriticalPathPacket BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro packet strongNormNormalConsistency consistencyObstructionRefusal refusalPkg
  obtain ⟨strongNormUnary, normalFormUnary, obstructionUnary, _handoffUnary,
    _dischargeSocketUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormRoute, _handoffObstructionSocket,
    _transportLocalName, provenancePkg⟩ := packet
  have consistencyUnary : UnaryHistory consistencyRead :=
    unary_cont_closed strongNormUnary normalFormUnary strongNormNormalConsistency
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed consistencyUnary obstructionUnary consistencyObstructionRefusal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
              hsame row refusalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle refusalRead pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro refusalRead ⟨hsame_refl refusalRead, refusalUnary⟩
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
      exact ⟨source.right, refusalPkg, provenancePkg⟩
  }
  exact ⟨cert, consistencyUnary, refusalUnary, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
