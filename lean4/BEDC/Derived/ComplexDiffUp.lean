import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Unary

namespace BEDC.Derived.ComplexDiffUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def CplxNonZero (h : BHist) : Prop :=
  hsame h BHist.Empty -> False

def CplxDiffQuot (f z h q : BHist) : Prop :=
  UnaryHistory f ∧ UnaryHistory z ∧ CplxNonZero h ∧ UnaryHistory q ∧ Cont f h q

theorem CplxDiffQuot_hsame_transport {f f' z z' h h' q q' : BHist} :
    hsame f f' -> hsame z z' -> hsame h h' -> hsame q q' ->
      CplxDiffQuot f z h q ->
        CplxDiffQuot f' z' h' q' ∧ UnaryHistory z' ∧ CplxNonZero h' ∧
          Cont f' h' q' := by
  intro sameF sameZ sameH sameQ quotient
  cases quotient with
  | intro functionCarrier rest =>
      cases rest with
      | intro pointCarrier rest =>
          cases rest with
          | intro stepNonzero rest =>
              cases rest with
              | intro quotientCarrier ledger =>
                  have functionCarrier' : UnaryHistory f' :=
                    unary_transport functionCarrier sameF
                  have pointCarrier' : UnaryHistory z' :=
                    unary_transport pointCarrier sameZ
                  have quotientCarrier' : UnaryHistory q' :=
                    unary_transport quotientCarrier sameQ
                  have stepNonzero' : CplxNonZero h' := by
                    intro stepEmpty
                    exact stepNonzero (hsame_trans sameH stepEmpty)
                  have ledger' : Cont f' h' q' :=
                    cont_hsame_transport sameF sameH sameQ ledger
                  exact And.intro
                    (And.intro functionCarrier'
                      (And.intro pointCarrier'
                        (And.intro stepNonzero'
                          (And.intro quotientCarrier' ledger'))))
                    (And.intro pointCarrier'
                      (And.intro stepNonzero' ledger'))

end BEDC.Derived.ComplexDiffUp
