import BEDC.Derived.ComplexSeriesUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.ComplexSeriesUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
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

theorem ComplexAbsConv_complexSeriesConv_of_pointwise_hsame {zero bound : BHist}
    {modulus c : BHist -> BHist} :
    (forall {n : BHist}, UnaryHistory n -> hsame (modulus n) (c n)) ->
      ComplexAbsConv zero modulus bound -> ComplexSeriesConv zero c bound := by
  intro pointwise absConv
  cases absConv with
  | intro absps absRest =>
      cases absRest with
      | intro N absRest =>
          cases absRest with
          | intro M data =>
              refine Exists.intro absps ?_
              refine Exists.intro N ?_
              refine Exists.intro M ?_
              constructor
              · intro n unaryN
                have convert :
                    forall {n S : BHist}, UnaryHistory n ->
                      ComplexAbsPartSum zero modulus n S -> ComplexPartSum zero c n S := by
                  intro n S unaryIndex absRow
                  induction absRow with
                  | zero =>
                      exact ComplexPartSum.zero
                  | step previous stepContinuation ih =>
                      have unaryPrevious : UnaryHistory _ := unary_e1_inversion unaryIndex
                      have sameTerm := pointwise unaryPrevious
                      have convertedStep : Cont _ (c _) _ :=
                        cont_hsame_transport (hsame_refl _) sameTerm (hsame_refl _)
                          stepContinuation
                      exact ComplexPartSum.step (ih unaryPrevious) convertedStep
                have absRow : ComplexAbsPartSum zero modulus n (absps n) :=
                  data.left n unaryN
                exact convert unaryN absRow
              · exact data.right

theorem ComplexAbsConv_complexSeriesConv {modulus : BHist -> BHist} {bound : BHist} :
    ComplexAbsConv BHist.Empty modulus bound ->
      ComplexSeriesConv BHist.Empty modulus bound := by
  intro absConv
  exact ComplexAbsConv_complexSeriesConv_of_pointwise_hsame
    (fun {n : BHist} _unaryN => hsame_refl (modulus n)) absConv

end BEDC.Derived.ComplexSeriesUp
