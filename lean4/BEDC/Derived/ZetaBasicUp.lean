import BEDC.Derived.DirichletSeriesUp

namespace BEDC.Derived.ZetaBasicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.DirichletSeriesUp

def ZetaBasicUnitTerm (_n s : BHist) : BHist := BHist.e1 s

def ZetaBasicPartSum (s n z : BHist) : Prop :=
  DirichletPartSum ZetaBasicUnitTerm s n z

theorem ZetaBasicPartSum_unary_result {s n z : BHist} :
    UnaryHistory s -> UnaryHistory n -> ZetaBasicPartSum s n z -> UnaryHistory z := by
  intro unaryS unaryN sum
  induction sum with
  | zero =>
      exact unary_empty
  | step previous stepCont ih =>
      have unaryPreviousIndex : UnaryHistory _ := unary_e1_inversion unaryN
      have unaryPreviousSum : UnaryHistory _ := ih unaryPreviousIndex
      have unaryTerm : UnaryHistory (BHist.e1 s) := unary_e1_closed unaryS
      exact unary_cont_closed unaryPreviousSum unaryTerm stepCont

theorem ZetaBasicPartSum_successor_result_nonempty {s n z : BHist} :
    ZetaBasicPartSum s (BHist.e1 n) z -> (hsame z BHist.Empty -> False) := by
  intro sum sameEmpty
  cases sum with
  | step _previous stepCont =>
      have emptyStep : Cont _ (ZetaBasicUnitTerm n s) BHist.Empty :=
        cont_result_hsame_transport stepCont sameEmpty
      have endpoints := cont_empty_result_inversion emptyStep
      exact not_hsame_e1_empty endpoints.right

end BEDC.Derived.ZetaBasicUp
