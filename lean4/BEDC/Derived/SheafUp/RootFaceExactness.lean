import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def SheafRootFaceExactnessSource
    (ambient member overlap route germ sectionHist exactness : BHist) : Prop :=
  SheafBHistCoverNerveLedger ambient member overlap route germ ∧
    SheafRootFaceRead overlap germ SheafRootFaceLanding.restrictionRoute ∧
      Cont germ sectionHist exactness ∧ UnaryHistory exactness

theorem SheafRootFaceExactnessSource_rows
    {ambient member overlap route germ sectionHist exactness : BHist} :
    SheafRootFaceExactnessSource ambient member overlap route germ sectionHist exactness ->
      SheafBHistCoverNerveLedger ambient member overlap route germ ∧
        SheafRootFaceRead overlap germ SheafRootFaceLanding.restrictionRoute ∧
          Cont germ sectionHist exactness ∧ UnaryHistory exactness := by
  intro source
  exact source

end BEDC.Derived.SheafUp
