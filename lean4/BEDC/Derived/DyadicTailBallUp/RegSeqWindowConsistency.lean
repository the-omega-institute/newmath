import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicTailBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicTailBallRegSeqWindowConsistency [AskSetup] [PackageSetup]
    {D F0 F1 B0 B1 R sharedWindow equalityRead0 equalityRead1 : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory D ->
      UnaryHistory F0 ->
        UnaryHistory F1 ->
          UnaryHistory R ->
            Cont D F0 B0 ->
              Cont D F1 B1 ->
                Cont B0 R sharedWindow ->
                  Cont B1 R sharedWindow ->
                    Cont sharedWindow R equalityRead0 ->
                      Cont sharedWindow R equalityRead1 ->
                        PkgSig bundle equalityRead0 pkg ->
                          PkgSig bundle equalityRead1 pkg ->
                            UnaryHistory B0 ∧ UnaryHistory B1 ∧
                              UnaryHistory sharedWindow ∧ UnaryHistory equalityRead0 ∧
                                UnaryHistory equalityRead1 ∧ Cont B0 R sharedWindow ∧
                                  Cont B1 R sharedWindow ∧
                                    PkgSig bundle equalityRead0 pkg ∧
                                      PkgSig bundle equalityRead1 pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro dUnary f0Unary f1Unary rUnary leftBallCont rightBallCont leftWindowCont
    rightWindowCont equalityCont0 equalityCont1 equalityPkg0 equalityPkg1
  have b0Unary : UnaryHistory B0 :=
    unary_cont_closed dUnary f0Unary leftBallCont
  have b1Unary : UnaryHistory B1 :=
    unary_cont_closed dUnary f1Unary rightBallCont
  have sharedWindowUnary : UnaryHistory sharedWindow :=
    unary_cont_closed b0Unary rUnary leftWindowCont
  have equalityUnary0 : UnaryHistory equalityRead0 :=
    unary_cont_closed sharedWindowUnary rUnary equalityCont0
  have equalityUnary1 : UnaryHistory equalityRead1 :=
    unary_cont_closed sharedWindowUnary rUnary equalityCont1
  exact
    ⟨b0Unary, b1Unary, sharedWindowUnary, equalityUnary0, equalityUnary1,
      leftWindowCont, rightWindowCont, equalityPkg0, equalityPkg1⟩

end BEDC.Derived.DyadicTailBallUp
