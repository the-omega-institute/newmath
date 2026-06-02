import BEDC.Derived.ModulusContinuityUp.DoubleCompositionRoute

namespace BEDC.Derived.ModulusContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ModulusContinuityCompositionAssociativityRoute [AskSetup] [PackageSetup]
    {dh kh sh dg kg sg df kf rf leftOuter leftMiddle leftInner rightOuter rightMiddle
      rightInner finalRead : BHist} :
    UnaryHistory dh →
      UnaryHistory kh →
        UnaryHistory sh →
          UnaryHistory dg →
            UnaryHistory kg →
              UnaryHistory sg →
                UnaryHistory df →
                  UnaryHistory kf →
                    Cont dh kh leftOuter →
                      Cont leftOuter sh leftMiddle →
                        Cont leftMiddle dg leftInner →
                          Cont leftInner kg finalRead →
                            Cont dh kh rightOuter →
                              Cont rightOuter sh rightMiddle →
                                Cont rightMiddle dg rightInner →
                                  Cont rightInner kg finalRead →
                                    hsame leftOuter rightOuter →
                                      hsame leftMiddle rightMiddle →
                                        hsame leftInner rightInner →
                                          UnaryHistory finalRead ∧
                                            hsame leftOuter rightOuter ∧
                                              hsame leftMiddle rightMiddle ∧
                                                hsame leftInner rightInner := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory hsame
  intro dhUnary khUnary shUnary dgUnary kgUnary _sgUnary _dfUnary _kfUnary leftDhKh
    leftOuterSh leftMiddleDg leftInnerKg _rightDhKh _rightOuterSh _rightMiddleDg
    _rightInnerKg sameOuter sameMiddle sameInner
  have leftOuterUnary : UnaryHistory leftOuter :=
    unary_cont_closed dhUnary khUnary leftDhKh
  have leftMiddleUnary : UnaryHistory leftMiddle :=
    unary_cont_closed leftOuterUnary shUnary leftOuterSh
  have leftInnerUnary : UnaryHistory leftInner :=
    unary_cont_closed leftMiddleUnary dgUnary leftMiddleDg
  have finalReadUnary : UnaryHistory finalRead :=
    unary_cont_closed leftInnerUnary kgUnary leftInnerKg
  exact ⟨finalReadUnary, sameOuter, sameMiddle, sameInner⟩

end BEDC.Derived.ModulusContinuityUp
