import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.RealIntegerPartUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

inductive RealIntegerPartUp : Type where
  | mk :
      (source bound bracket intCandidate residual dyadicScale streamWindow readback
        transport replay provenance nameRow : BHist) →
        RealIntegerPartUp
  deriving DecidableEq

def RealIntegerPartCarrier [AskSetup] [PackageSetup]
    (source bound bracket intCandidate residual dyadicScale streamWindow readback
      transport replay provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧
    UnaryHistory bound ∧
      UnaryHistory bracket ∧
        UnaryHistory intCandidate ∧
          UnaryHistory residual ∧
            UnaryHistory dyadicScale ∧
              UnaryHistory streamWindow ∧
                UnaryHistory readback ∧
                  UnaryHistory transport ∧
                    UnaryHistory replay ∧
                      UnaryHistory provenance ∧
                        UnaryHistory nameRow ∧ PkgSig bundle nameRow pkg

theorem RealIntegerPartCarrier_bracket_route [AskSetup] [PackageSetup]
    {source bound bracket intCandidate residual dyadicScale streamWindow readback
      transport replay provenance nameRow decimalRead approxRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealIntegerPartCarrier source bound bracket intCandidate residual dyadicScale streamWindow
        readback transport replay provenance nameRow bundle pkg →
      Cont replay source decimalRead →
        Cont decimalRead bracket approxRead →
          PkgSig bundle approxRead pkg →
            UnaryHistory source ∧
              UnaryHistory bound ∧
                UnaryHistory bracket ∧
                  UnaryHistory intCandidate ∧
                    UnaryHistory residual ∧
                      UnaryHistory dyadicScale ∧
                        UnaryHistory streamWindow ∧
                          UnaryHistory readback ∧
                            UnaryHistory decimalRead ∧
                              UnaryHistory approxRead ∧
                                Cont replay source decimalRead ∧
                                  Cont decimalRead bracket approxRead ∧
                                    PkgSig bundle nameRow pkg ∧
                                      PkgSig bundle approxRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier replaySource decimalBracket approxPkg
  cases carrier with
  | intro sourceUnary rest0 =>
      cases rest0 with
      | intro boundUnary rest1 =>
          cases rest1 with
          | intro bracketUnary rest2 =>
              cases rest2 with
              | intro intCandidateUnary rest3 =>
                  cases rest3 with
                  | intro residualUnary rest4 =>
                      cases rest4 with
                      | intro dyadicScaleUnary rest5 =>
                          cases rest5 with
                          | intro streamWindowUnary rest6 =>
                              cases rest6 with
                              | intro readbackUnary rest7 =>
                                  cases rest7 with
                                  | intro _transportUnary rest8 =>
                                      cases rest8 with
                                      | intro replayUnary rest9 =>
                                          cases rest9 with
                                          | intro _provenanceUnary rest10 =>
                                              cases rest10 with
                                              | intro _nameRowUnary namePkg =>
                                                  have decimalUnary :
                                                      UnaryHistory decimalRead :=
                                                    unary_cont_closed replayUnary sourceUnary
                                                      replaySource
                                                  have approxUnary :
                                                      UnaryHistory approxRead :=
                                                    unary_cont_closed decimalUnary bracketUnary
                                                      decimalBracket
                                                  exact
                                                    ⟨sourceUnary, boundUnary, bracketUnary,
                                                      intCandidateUnary, residualUnary,
                                                      dyadicScaleUnary, streamWindowUnary,
                                                      readbackUnary, decimalUnary, approxUnary,
                                                      replaySource, decimalBracket, namePkg,
                                                      approxPkg⟩

end BEDC.Derived.RealIntegerPartUp
