import BEDC.FKernel.Cont
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.GaloisExtUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem GaloisExtClassifier_transport_row
    {field field' separable separable' normal normal' sepFace sepFace' classifier classifier'
      ledger ledger' : BHist} :
    UnaryHistory field' ->
      UnaryHistory separable' ->
        UnaryHistory normal' ->
          UnaryHistory sepFace' ->
            hsame field field' ->
              hsame separable separable' ->
                hsame normal normal' ->
                  hsame sepFace sepFace' ->
                    Cont field separable classifier ->
                      Cont field' separable' classifier' ->
                        Cont normal sepFace ledger ->
                          Cont normal' sepFace' ledger' ->
                            UnaryHistory classifier' ∧
                              UnaryHistory ledger' ∧
                                hsame classifier classifier' ∧ hsame ledger ledger' := by
  intro fieldUnary separableUnary normalUnary sepFaceUnary fieldSame separableSame normalSame
    sepFaceSame classifierCont classifierCont' ledgerCont ledgerCont'
  constructor
  · exact unary_cont_closed fieldUnary separableUnary classifierCont'
  · constructor
    · exact unary_cont_closed normalUnary sepFaceUnary ledgerCont'
    · constructor
      · exact cont_respects_hsame fieldSame separableSame classifierCont classifierCont'
      · exact cont_respects_hsame normalSame sepFaceSame ledgerCont ledgerCont'

end BEDC.Derived.GaloisExtUp
