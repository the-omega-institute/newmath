import BEDC.Derived.HaltingDiagonalUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Ext

namespace BEDC.Derived.HaltingDiagonalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Cont
open BEDC.FKernel.Ext

theorem HaltingDiagonal_fixed_point_package_rows (z : HaltingDiagonalUp) :
    ∃ program input selfReference fixedContinuation diagonalPolicy transport routes provenance
        nameCert : BHist,
      z =
          HaltingDiagonalUp.mk program input selfReference fixedContinuation diagonalPolicy transport
            routes provenance nameCert ∧
        Ext selfReference BMark.b0 (BHist.e0 selfReference) ∧
          Cont (BHist.e0 selfReference) fixedContinuation
            (append (BHist.e0 selfReference) fixedContinuation) := by
  -- BEDC touchpoint anchor: BHist BMark
  cases z with
  | mk program input selfReference fixedContinuation diagonalPolicy transport routes provenance
      nameCert =>
      exact
        ⟨program, input, selfReference, fixedContinuation, diagonalPolicy, transport, routes,
          provenance, nameCert, rfl, Ext.e0 selfReference, rfl⟩

end BEDC.Derived.HaltingDiagonalUp
