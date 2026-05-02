import BEDC.Derived.CompactUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CompactUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CompactNetWitness_semanticNameCert {center precision : BHist}
    (centerCarrier : UnaryHistory center) (precisionCarrier : UnaryHistory precision) :
    BEDC.FKernel.NameCert.SemanticNameCert (CompactNetWitness center precision)
      (CompactNetWitness center precision) (CompactNetWitness center precision) hsame := by
  constructor
  · constructor
    · exact
        Exists.intro (append center precision)
          (And.intro centerCarrier
            (And.intro precisionCarrier
              (And.intro (unary_append_closed centerCarrier precisionCarrier) (cont_intro rfl))))
    · intro h _witness
      exact hsame_refl h
    · intro h k same
      exact hsame_symm same
    · intro h k r sameHK sameKR
      exact hsame_trans sameHK sameKR
    · intro h k same witness
      cases same
      exact witness
  · intro h source
    exact source
  · intro h source
    exact source

end BEDC.Derived.CompactUp
