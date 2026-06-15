import BEDC.Derived.LimitUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LimitCarrier_completion_scope_refusal [AskSetup] [PackageSetup]
    {S R D A T C H P N windowRead toleranceRead sealRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    limitFields (LimitUp.mk S R D A T C H P N) = [S, R, D, A, T, C, H, P, N] →
      UnaryHistory S →
        UnaryHistory R →
          UnaryHistory D →
            UnaryHistory A →
              UnaryHistory C →
                Cont S R windowRead →
                  Cont windowRead D toleranceRead →
                    Cont toleranceRead A sealRead →
                      Cont sealRead C replayRead →
                        PkgSig bundle P pkg →
                          PkgSig bundle N pkg →
                            UnaryHistory windowRead ∧ UnaryHistory toleranceRead ∧
                              UnaryHistory sealRead ∧ UnaryHistory replayRead ∧
                                Cont S R windowRead ∧ Cont windowRead D toleranceRead ∧
                                  Cont toleranceRead A sealRead ∧ Cont sealRead C replayRead ∧
                                    PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: LimitUp BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro fieldRows sUnary rUnary dUnary aUnary cUnary windowRoute toleranceRoute sealRoute
    replayRoute provenancePkg namePkg
  cases fieldRows
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed sUnary rUnary windowRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed windowUnary dUnary toleranceRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceUnary aUnary sealRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed sealUnary cUnary replayRoute
  exact
    ⟨windowUnary, toleranceUnary, sealUnary, replayUnary, windowRoute, toleranceRoute,
      sealRoute, replayRoute, provenancePkg, namePkg⟩

end BEDC.Derived.LimitUp
