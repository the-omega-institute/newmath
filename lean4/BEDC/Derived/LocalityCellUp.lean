import BEDC.Derived.LocalityCellUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Package

namespace BEDC.Derived.LocalityCellUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

def LocalityCellPacket [AskSetup] [PackageSetup]
    (observerLeft observerRight recordLeft recordRight gapLeft gapRight _transport route package
      name : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  Cont observerLeft recordLeft gapLeft ∧
    Cont observerRight recordRight gapRight ∧
      Cont gapLeft gapRight route ∧ PkgSig bundle package pkg ∧ PkgSig bundle name pkg

theorem LocalityCellPacket_interobserver_readback [AskSetup] [PackageSetup]
    {observerLeft observerLeft' observerRight observerRight' recordLeft recordLeft' recordRight
      recordRight' gapLeft gapLeft' gapRight gapRight' transport route package name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocalityCellPacket observerLeft observerRight recordLeft recordRight gapLeft gapRight
        transport route package name bundle pkg →
      hsame observerLeft observerLeft' →
        hsame observerRight observerRight' →
          hsame recordLeft recordLeft' →
            hsame recordRight recordRight' →
              Cont observerLeft' recordLeft' gapLeft' →
                Cont observerRight' recordRight' gapRight' →
                  hsame gapLeft gapLeft' ∧ hsame gapRight gapRight' ∧
                    Cont gapLeft gapRight route ∧ PkgSig bundle package pkg ∧
                      PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame Pkg ProbeBundle
  intro packet sameObserverLeft sameObserverRight sameRecordLeft sameRecordRight
    leftReadback rightReadback
  obtain ⟨leftRoute, rightRoute, gapRoute, packagePkg, namePkg⟩ := packet
  have sameGapLeft : hsame gapLeft gapLeft' :=
    cont_respects_hsame sameObserverLeft sameRecordLeft leftRoute leftReadback
  have sameGapRight : hsame gapRight gapRight' :=
    cont_respects_hsame sameObserverRight sameRecordRight rightRoute rightReadback
  exact ⟨sameGapLeft, sameGapRight, gapRoute, packagePkg, namePkg⟩

end BEDC.Derived.LocalityCellUp
