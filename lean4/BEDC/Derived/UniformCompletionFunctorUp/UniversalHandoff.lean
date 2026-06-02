import BEDC.Derived.UniformCompletionFunctorUp.TasteGate
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.UniformCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCompletionFunctorUniversalHandoff [AskSetup] [PackageSetup]
    {U F E R W D S H C P N sourceHandoff extensionRead regseqRead windowRead dyadicRead
      sealRead transported replayed sourced named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory U ->
      UnaryHistory F ->
        UnaryHistory E ->
          UnaryHistory R ->
            UnaryHistory W ->
              UnaryHistory D ->
                UnaryHistory S ->
                  UnaryHistory H ->
                    UnaryHistory C ->
                      UnaryHistory P ->
                        UnaryHistory N ->
                          Cont U F sourceHandoff ->
                            Cont sourceHandoff E extensionRead ->
                              Cont extensionRead R regseqRead ->
                                Cont extensionRead W windowRead ->
                                  Cont windowRead D dyadicRead ->
                                    Cont dyadicRead S sealRead ->
                                      Cont sealRead H transported ->
                                        Cont transported C replayed ->
                                          Cont replayed P sourced ->
                                            Cont sourced N named ->
                                              PkgSig bundle named pkg ->
                                                UnaryHistory sourceHandoff ∧
                                                  UnaryHistory extensionRead ∧
                                                    UnaryHistory regseqRead ∧
                                                      UnaryHistory windowRead ∧
                                                        UnaryHistory dyadicRead ∧
                                                          UnaryHistory sealRead ∧
                                                            UnaryHistory transported ∧
                                                              UnaryHistory replayed ∧
                                                                UnaryHistory sourced ∧
                                                                  UnaryHistory named ∧
                                                                    PkgSig bundle named pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro uUnary fUnary eUnary rUnary wUnary dUnary sUnary hUnary cUnary pUnary nUnary
    sourceCont extensionCont regseqCont windowCont dyadicCont sealCont transportedCont
    replayedCont sourcedCont namedCont namedPkg
  have sourceUnary : UnaryHistory sourceHandoff :=
    unary_cont_closed uUnary fUnary sourceCont
  have extensionUnary : UnaryHistory extensionRead :=
    unary_cont_closed sourceUnary eUnary extensionCont
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed extensionUnary rUnary regseqCont
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed extensionUnary wUnary windowCont
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed windowUnary dUnary dyadicCont
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed dyadicUnary sUnary sealCont
  have transportedUnary : UnaryHistory transported :=
    unary_cont_closed sealUnary hUnary transportedCont
  have replayedUnary : UnaryHistory replayed :=
    unary_cont_closed transportedUnary cUnary replayedCont
  have sourcedUnary : UnaryHistory sourced :=
    unary_cont_closed replayedUnary pUnary sourcedCont
  have namedUnary : UnaryHistory named :=
    unary_cont_closed sourcedUnary nUnary namedCont
  exact
    ⟨sourceUnary, extensionUnary, regseqUnary, windowUnary, dyadicUnary, sealUnary,
      transportedUnary, replayedUnary, sourcedUnary, namedUnary, namedPkg⟩

end BEDC.Derived.UniformCompletionFunctorUp
