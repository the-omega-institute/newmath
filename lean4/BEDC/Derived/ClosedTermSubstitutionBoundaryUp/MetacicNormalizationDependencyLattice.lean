import BEDC.Derived.ClosedTermSubstitutionBoundaryUp
import BEDC.FKernel.Package

namespace BEDC.Derived.ClosedTermSubstitutionBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryMetacicNormalizationDependencyLattice
    [AskSetup] [PackageSetup]
    {closedSubstitution sealRow criticalSocket router handoff endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory closedSubstitution ->
      UnaryHistory sealRow ->
        UnaryHistory criticalSocket ->
          UnaryHistory router ->
            Cont closedSubstitution sealRow criticalSocket ->
              Cont criticalSocket router handoff ->
                Cont handoff router endpoint ->
                  PkgSig bundle endpoint pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row closedSubstitution ∨ hsame row sealRow ∨
                            hsame row criticalSocket ∨ hsame row router ∨
                              hsame row endpoint)
                        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle endpoint pkg)
                        hsame ∧
                      UnaryHistory handoff ∧ UnaryHistory endpoint := by
  -- BEDC touchpoint anchor: BHist Cont Pkg SemanticNameCert hsame UnaryHistory
  intro unaryClosed unarySeal unaryCritical unaryRouter closedSeal criticalRouter
    handoffRouter endpointPkg
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed unaryCritical unaryRouter criticalRouter
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed handoffUnary unaryRouter handoffRouter
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row closedSubstitution ∨ hsame row sealRow ∨
              hsame row criticalSocket ∨ hsame row router ∨ hsame row endpoint)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle endpoint pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint ⟨hsame_refl endpoint, endpointUnary⟩
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
      right; right; right; right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, endpointPkg⟩
  }
  exact ⟨cert, handoffUnary, endpointUnary⟩

end BEDC.Derived.ClosedTermSubstitutionBoundaryUp
