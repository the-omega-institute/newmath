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

theorem CellularBoundaryConditionNonescapeBoundary [AskSetup] [PackageSetup]
    {E W R A H C P N publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    cellularBoundaryConditionFields (CellularBoundaryConditionUp.mk E W R A H C P N) =
        [E, W, R, A, H, C, P, N] →
      Cont E W R →
        Cont R A publicRead →
          PkgSig bundle N pkg →
            SemanticNameCert
              (fun row : BHist =>
                hsame row publicRead ∧
                  ∃ packet : CellularBoundaryConditionUp,
                    packet = CellularBoundaryConditionUp.mk E W R A H C P N ∧
                      cellularBoundaryConditionFields packet = [E, W, R, A, H, C, P, N])
              (fun row : BHist => Cont E W R ∧ Cont R A row)
              (fun row : BHist => hsame row publicRead ∧ PkgSig bundle N pkg ∧ hsame H H)
              hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro boundaryFields edgeRoute publicRoute packageName
  exact {
    core := {
      carrier_inhabited := by
        exact
          ⟨publicRead, hsame_refl publicRead,
            CellularBoundaryConditionUp.mk E W R A H C P N, rfl, boundaryFields⟩
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
      intro row source
      cases source.left
      exact ⟨edgeRoute, publicRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, packageName, hsame_refl H⟩
  }

end BEDC.Derived.CellularBoundaryConditionUp
