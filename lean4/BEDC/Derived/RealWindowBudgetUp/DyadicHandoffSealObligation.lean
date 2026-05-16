import BEDC.Derived.RealWindowBudgetUp

namespace BEDC.Derived.RealWindowBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealWindowBudgetCarrier_dyadic_handoff_seal_obligation [AskSetup]
    [PackageSetup]
    {request windows dyadic handoff realSeal selector disclosure transport route provenance
      nameRow dyadicRead handoffRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealWindowBudgetCarrier request windows dyadic handoff realSeal selector disclosure
        transport route provenance nameRow bundle pkg →
      Cont windows dyadic dyadicRead →
        Cont dyadicRead handoff handoffRead →
          Cont handoffRead realSeal sealRead →
            PkgSig bundle sealRead pkg →
              UnaryHistory windows ∧ UnaryHistory dyadic ∧ UnaryHistory handoff ∧
                UnaryHistory realSeal ∧ UnaryHistory dyadicRead ∧ UnaryHistory handoffRead ∧
                  UnaryHistory sealRead ∧ Cont windows dyadic dyadicRead ∧
                    Cont dyadicRead handoff handoffRead ∧
                      Cont handoffRead realSeal sealRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier windowsDyadicRead dyadicReadHandoffRead handoffReadSealRead sealReadPkg
  have dyadicReadUnary : UnaryHistory dyadicRead :=
    unary_cont_closed carrier.windows_unary carrier.dyadic_unary windowsDyadicRead
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed dyadicReadUnary carrier.handoff_unary dyadicReadHandoffRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed handoffReadUnary carrier.realSeal_unary handoffReadSealRead
  exact
    ⟨carrier.windows_unary, carrier.dyadic_unary, carrier.handoff_unary,
      carrier.realSeal_unary, dyadicReadUnary, handoffReadUnary, sealReadUnary,
      windowsDyadicRead, dyadicReadHandoffRead, handoffReadSealRead, carrier.provenance_pkg,
      sealReadPkg⟩

end BEDC.Derived.RealWindowBudgetUp
