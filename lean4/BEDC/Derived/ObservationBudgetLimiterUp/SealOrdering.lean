import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary

namespace BEDC.Derived.ObservationBudgetLimiterUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem ObservationBudgetLimiter_seal_ordering
    {E B K W D R S EB BK KW WD DR RS : BHist} :
    UnaryHistory E →
      UnaryHistory B →
        UnaryHistory K →
          UnaryHistory W →
            UnaryHistory D →
              UnaryHistory R →
                UnaryHistory S →
                  Cont E B EB →
                    Cont EB K BK →
                      Cont BK W KW →
                        Cont KW D WD →
                          Cont WD R DR →
                            Cont DR S RS →
                              UnaryHistory EB ∧ UnaryHistory BK ∧ UnaryHistory KW ∧
                                UnaryHistory WD ∧ UnaryHistory DR ∧ UnaryHistory RS ∧
                                  Cont E B EB ∧ Cont EB K BK ∧ Cont BK W KW ∧
                                    Cont KW D WD ∧ Cont WD R DR ∧ Cont DR S RS := by
  -- BEDC touchpoint anchor: BHist Cont
  intro uE uB uK uW uD uR uS cEB cBK cKW cWD cDR cRS
  have uEB : UnaryHistory EB := unary_cont_closed uE uB cEB
  have uBK : UnaryHistory BK := unary_cont_closed uEB uK cBK
  have uKW : UnaryHistory KW := unary_cont_closed uBK uW cKW
  have uWD : UnaryHistory WD := unary_cont_closed uKW uD cWD
  have uDR : UnaryHistory DR := unary_cont_closed uWD uR cDR
  have uRS : UnaryHistory RS := unary_cont_closed uDR uS cRS
  constructor
  · exact uEB
  · constructor
    · exact uBK
    · constructor
      · exact uKW
      · constructor
        · exact uWD
        · constructor
          · exact uDR
          · constructor
            · exact uRS
            · constructor
              · exact cEB
              · constructor
                · exact cBK
                · constructor
                  · exact cKW
                  · constructor
                    · exact cWD
                    · constructor
                      · exact cDR
                      · exact cRS

end BEDC.Derived.ObservationBudgetLimiterUp
