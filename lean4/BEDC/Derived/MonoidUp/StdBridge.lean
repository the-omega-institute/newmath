import BEDC.Derived.MonoidUp

namespace BEDC.Derived.MonoidUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.NameCert

theorem MonoidUp_StdBridge :
    SemanticNameCert UnaryHistory UnaryHistory UnaryHistory
        (MonoidHistoryClassifier UnaryHistory) ∧
      (forall {h k r : BHist}, UnaryHistory h -> UnaryHistory k -> Cont h k r ->
        UnaryHistory r ∧ MonoidHistoryClassifier UnaryHistory r (append h k)) ∧
      (forall {h : BHist}, UnaryHistory h ->
        MonoidHistoryClassifier UnaryHistory (append BHist.Empty h) h ∧
          MonoidHistoryClassifier UnaryHistory (append h BHist.Empty) h) := by
  constructor
  · exact unary_append_monoid_semantic_name_certificate.left
  · constructor
    · intro h k r unaryH unaryK hcont
      have unaryR : UnaryHistory r :=
        unary_cont_closed unaryH unaryK hcont
      exact And.intro unaryR
        (And.intro unaryR
          (And.intro (unary_append_closed unaryH unaryK) hcont))
    · intro h unaryH
      exact And.intro
        (And.intro (unary_append_closed unary_empty unaryH)
          (And.intro unaryH (BEDC.FKernel.Cont.append_empty_left h)))
        (And.intro (unary_append_closed unaryH unary_empty)
          (And.intro unaryH (BEDC.FKernel.Cont.append_empty_right h)))

end BEDC.Derived.MonoidUp
