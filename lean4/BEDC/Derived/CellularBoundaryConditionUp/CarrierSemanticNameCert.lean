import BEDC.Derived.CellularBoundaryConditionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.CellularBoundaryConditionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem CellularBoundaryConditionCarrierSemanticNameCert [AskSetup] [PackageSetup]
    {E W R A H C P N route : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    cellularBoundaryConditionFields (CellularBoundaryConditionUp.mk E W R A H C P N) =
        [E, W, R, A, H, C, P, N] →
      Cont E W R →
        Cont R A route →
          PkgSig bundle N pkg →
            SemanticNameCert
              (fun row : BHist =>
                hsame row route ∧
                  ∃ packet : CellularBoundaryConditionUp,
                    packet = CellularBoundaryConditionUp.mk E W R A H C P N ∧
                      cellularBoundaryConditionFields packet = [E, W, R, A, H, C, P, N])
              (fun row : BHist => Cont E W R ∧ Cont R A row)
              (fun row : BHist => hsame row route ∧ PkgSig bundle N pkg)
              hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro fieldsExact edgeRoute routeRead namePkg
  exact {
    core := {
      carrier_inhabited := by
        exact
          ⟨route, hsame_refl route,
            CellularBoundaryConditionUp.mk E W R A H C P N, rfl, fieldsExact⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _row' leftSame rightSame
        exact hsame_trans leftSame rightSame
      carrier_respects_equiv := by
        intro _row _row' same source
        cases same
        exact source
    }
    pattern_sound := by
      intro _row source
      cases source.left
      exact ⟨edgeRoute, routeRead⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, namePkg⟩
  }

end BEDC.Derived.CellularBoundaryConditionUp
