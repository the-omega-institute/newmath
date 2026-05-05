import BEDC.Derived.ComplexSeriesUp

namespace BEDC.Derived.ComplexSeriesUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexLimitUp

def ComplexAbsConv (zero : BHist) (modulus : BHist -> BHist) (bound : BHist) : Prop :=
  exists absps : BHist -> BHist, exists N : BHist -> BHist, exists M : BHist -> BHist,
    (forall n : BHist, UnaryHistory n -> ComplexAbsPartSum zero modulus n (absps n)) /\
      ComplexLimit absps N bound M

theorem ComplexAbsPartSum_complexPartSum {zero : BHist} {modulus : BHist -> BHist}
    {n S : BHist} :
    ComplexAbsPartSum zero modulus n S -> ComplexPartSum zero modulus n S := by
  intro sum
  induction sum with
  | zero =>
      exact ComplexPartSum.zero
  | step previous stepCont ih =>
      exact ComplexPartSum.step ih stepCont

theorem ComplexAbsConv_complexSeriesConv {modulus : BHist -> BHist} {bound : BHist} :
    ComplexAbsConv BHist.Empty modulus bound ->
      ComplexSeriesConv BHist.Empty modulus bound := by
  intro absConv
  cases absConv with
  | intro absps absRest =>
      cases absRest with
      | intro N absRest =>
          cases absRest with
          | intro M absData =>
              exact Exists.intro absps
                (Exists.intro N
                  (Exists.intro M
                    (And.intro
                      (fun n unaryN =>
                        ComplexAbsPartSum_complexPartSum (absData.left n unaryN))
                      absData.right)))

end BEDC.Derived.ComplexSeriesUp
