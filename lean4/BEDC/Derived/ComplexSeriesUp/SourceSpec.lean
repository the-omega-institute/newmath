import BEDC.Derived.ComplexSeriesUp

namespace BEDC.Derived.ComplexSeriesUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexLimitUp
open BEDC.Derived.ComplexUp

def ComplexSeriesSourceSpec (zero : BHist) (c : BHist -> BHist) (S : BHist) : Prop :=
  UnaryHistory zero ∧ ComplexTermSeqCarrier c ∧ ComplexSeriesConv zero c S

theorem ComplexSeriesSourceSpec_limit_carrier {zero : BHist} {c : BHist -> BHist}
    {S : BHist} :
    ComplexSeriesSourceSpec zero c S ->
      UnaryHistory zero ∧ ComplexHistoryCarrier S ∧
        ∃ ps : BHist -> BHist, ∃ N : BHist -> BHist, ∃ M : BHist -> BHist,
          ComplexLimit ps N S M := by
  intro source
  unfold ComplexSeriesSourceSpec at source
  cases source with
  | intro zeroUnary rest =>
      cases rest with
      | intro _termCarrier conv =>
          cases conv with
          | intro ps convRest =>
              cases convRest with
              | intro N convRest =>
                  cases convRest with
                  | intro M data =>
                      exact And.intro zeroUnary
                        (And.intro data.right.right.left
                          (Exists.intro ps
                            (Exists.intro N
                              (Exists.intro M data.right))))

end BEDC.Derived.ComplexSeriesUp
