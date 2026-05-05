import BEDC.Derived.ComplexSeriesUp

namespace BEDC.Derived.ComplexSeriesUp

open BEDC.FKernel.Hist

def ComplexSeriesPatternSpec (zero : BHist) (c : BHist -> BHist) (S : BHist) : Prop :=
  exists ps : BHist -> BHist, exists N : BHist -> BHist, exists M : BHist -> BHist,
    ComplexSeriesConvWitness zero c ps N M S

theorem ComplexSeriesPatternSpec_complexSeriesConv {zero : BHist} {c : BHist -> BHist}
    {S : BHist} :
    ComplexSeriesPatternSpec zero c S -> ComplexSeriesConv zero c S := by
  intro pattern
  cases pattern with
  | intro ps patternRest =>
      cases patternRest with
      | intro N patternRest =>
          cases patternRest with
          | intro M witness =>
              exact Exists.intro ps
                (Exists.intro N
                  (Exists.intro M (And.intro witness.right.left witness.right.right)))

end BEDC.Derived.ComplexSeriesUp
