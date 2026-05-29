import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathRealRootBudgetLock [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName candidateRead l10Read socketRead budgetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route dischargeSocket candidateRead →
        Cont candidateRead localName l10Read →
          Cont candidateRead obstruction socketRead →
            Cont l10Read route budgetRead →
              PkgSig bundle l10Read pkg →
                PkgSig bundle socketRead pkg →
                  PkgSig bundle budgetRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row budgetRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row route ∨ hsame row dischargeSocket ∨
                            hsame row candidateRead ∨ hsame row l10Read ∨
                              hsame row socketRead ∨ hsame row budgetRead)
                        (fun row : BHist =>
                          hsame row budgetRead ∧ PkgSig bundle l10Read pkg ∧
                            PkgSig bundle socketRead pkg ∧ PkgSig bundle budgetRead pkg)
                        hsame ∧
                      UnaryHistory candidateRead ∧ UnaryHistory l10Read ∧
                        UnaryHistory socketRead ∧ UnaryHistory budgetRead ∧
                          PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro packet routeDischargeCandidate candidateLocalNameL10 candidateObstructionSocket
    l10RouteBudget l10Pkg socketPkg budgetPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _handoffUnary,
    dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed routeUnary dischargeSocketUnary routeDischargeCandidate
  have l10Unary : UnaryHistory l10Read :=
    unary_cont_closed candidateUnary localNameUnary candidateLocalNameL10
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed candidateUnary obstructionUnary candidateObstructionSocket
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed l10Unary routeUnary l10RouteBudget
  have sourceBudget :
      (fun row : BHist => hsame row budgetRead ∧ UnaryHistory row) budgetRead := by
    exact ⟨hsame_refl budgetRead, budgetUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row budgetRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row route ∨ hsame row dischargeSocket ∨ hsame row candidateRead ∨
              hsame row l10Read ∨ hsame row socketRead ∨ hsame row budgetRead)
          (fun row : BHist =>
            hsame row budgetRead ∧ PkgSig bundle l10Read pkg ∧
              PkgSig bundle socketRead pkg ∧ PkgSig bundle budgetRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro budgetRead sourceBudget
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, l10Pkg, socketPkg, budgetPkg⟩
  }
  exact ⟨cert, candidateUnary, l10Unary, socketUnary, budgetUnary, provenancePkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
