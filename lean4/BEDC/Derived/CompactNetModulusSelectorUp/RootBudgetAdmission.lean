import BEDC.Derived.CompactNetModulusSelectorUp.KernelCarrier

namespace BEDC.Derived.CompactNetModulusSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactNetModulusSelectorRootBudgetAdmission [AskSetup] [PackageSetup]
    {source target tolerance probes centers radii moduli fold precision transport route
      provenance localName compactRead radiusRead modulusRead precisionRead budgetRead :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactNetModulusSelectorCarrier source target tolerance probes centers radii moduli
        fold precision transport route provenance localName bundle pkg →
      Cont source probes compactRead →
        Cont centers radii radiusRead →
          Cont moduli fold modulusRead →
            Cont precision route precisionRead →
              Cont precisionRead localName budgetRead →
                PkgSig bundle budgetRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row budgetRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row probes ∨ hsame row centers ∨ hsame row radii ∨
                          hsame row moduli ∨ hsame row fold ∨ hsame row precision ∨
                            hsame row budgetRead)
                      (fun row : BHist =>
                        PkgSig bundle provenance pkg ∧ PkgSig bundle budgetRead pkg ∧
                          hsame row budgetRead)
                      hsame ∧
                    UnaryHistory compactRead ∧ UnaryHistory radiusRead ∧
                      UnaryHistory modulusRead ∧ UnaryHistory precisionRead ∧
                        UnaryHistory budgetRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier sourceProbesCompact centersRadiiRadius moduliFoldModulus
    precisionRouteRead precisionReadNameBudget budgetReadPkg
  obtain ⟨sourceUnary, _targetUnary, _toleranceUnary, probesUnary, centersUnary,
    radiiUnary, moduliUnary, foldUnary, precisionUnary, _transportUnary, routeUnary,
    provenanceUnary, localNameUnary, _carrierSourceProbesCenters,
    _carrierModuliFoldPrecision, _carrierPrecisionRouteName, provenancePkg⟩ := carrier
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed sourceUnary probesUnary sourceProbesCompact
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed centersUnary radiiUnary centersRadiiRadius
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed moduliUnary foldUnary moduliFoldModulus
  have precisionReadUnary : UnaryHistory precisionRead :=
    unary_cont_closed precisionUnary routeUnary precisionRouteRead
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed precisionReadUnary localNameUnary precisionReadNameBudget
  have sourceBudgetRead :
      (fun row : BHist => hsame row budgetRead ∧ UnaryHistory row) budgetRead := by
    exact ⟨hsame_refl budgetRead, budgetReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row budgetRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row probes ∨ hsame row centers ∨ hsame row radii ∨
              hsame row moduli ∨ hsame row fold ∨ hsame row precision ∨
                hsame row budgetRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle budgetRead pkg ∧
              hsame row budgetRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro budgetRead sourceBudgetRead
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, budgetReadPkg, source.left⟩
  }
  exact
    ⟨cert, compactReadUnary, radiusReadUnary, modulusReadUnary, precisionReadUnary,
      budgetReadUnary⟩

end BEDC.Derived.CompactNetModulusSelectorUp
