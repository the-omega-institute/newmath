import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathRouteExhaustion [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName routeRead socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont strongNorm normalForm routeRead →
        Cont handoff obstruction socketRead →
          PkgSig bundle routeRead pkg →
            PkgSig bundle socketRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row routeRead ∨ hsame row socketRead) ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
                      hsame row handoff ∨ hsame row dischargeSocket ∨ hsame row transport ∨
                        hsame row route ∨ hsame row provenance ∨ hsame row localName ∨
                          hsame row routeRead ∨ hsame row socketRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle routeRead pkg ∧
                      PkgSig bundle socketRead pkg ∧ PkgSig bundle provenance pkg)
                  hsame ∧
                UnaryHistory routeRead ∧ UnaryHistory socketRead := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro packet routeReadCont socketReadCont routeReadPkg socketReadPkg
  obtain ⟨strongNormUnary, normalFormUnary, obstructionUnary, handoffUnary,
    _dischargeSocketUnary, _transportUnary, _routeUnary, provenanceUnary, _localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed strongNormUnary normalFormUnary routeReadCont
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed handoffUnary obstructionUnary socketReadCont
  have sourceRouteRead :
      (fun row : BHist =>
        (hsame row routeRead ∨ hsame row socketRead) ∧ UnaryHistory row) routeRead := by
    exact ⟨Or.inl (hsame_refl routeRead), routeReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row routeRead ∨ hsame row socketRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
              hsame row handoff ∨ hsame row dischargeSocket ∨ hsame row transport ∨
                hsame row route ∨ hsame row provenance ∨ hsame row localName ∨
                  hsame row routeRead ∨ hsame row socketRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle routeRead pkg ∧
              PkgSig bundle socketRead pkg ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro routeRead sourceRouteRead
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
        constructor
        · cases source.left with
          | inl routeSame =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) routeSame)
          | inr socketSame =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) socketSame)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl routeSame =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr (Or.inl routeSame)))))))))
      | inr socketSame =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr (Or.inr socketSame)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, routeReadPkg, socketReadPkg, provenancePkg⟩
  }
  exact ⟨cert, routeReadUnary, socketReadUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
