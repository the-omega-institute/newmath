import BEDC.Derived.RealWindowBudgetUp

namespace BEDC.Derived.RealWindowBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealWindowBudgetCarrier_finite_tail_filter_handoff [AskSetup] [PackageSetup]
    {request windows dyadic handoff realSeal selector disclosure transport route provenance
      nameRow tailWindow tailRegSeq tailSeal tailRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealWindowBudgetCarrier request windows dyadic handoff realSeal selector disclosure
        transport route provenance nameRow bundle pkg →
      Cont windows dyadic tailWindow →
        Cont tailWindow handoff tailRegSeq →
          Cont tailRegSeq realSeal tailSeal →
            Cont tailSeal route tailRead →
              PkgSig bundle tailRead pkg →
                UnaryHistory windows ∧ UnaryHistory dyadic ∧ UnaryHistory handoff ∧
                  UnaryHistory realSeal ∧ UnaryHistory tailWindow ∧
                    UnaryHistory tailRegSeq ∧ UnaryHistory tailSeal ∧
                      UnaryHistory tailRead ∧ Cont windows dyadic tailWindow ∧
                        Cont tailWindow handoff tailRegSeq ∧
                          Cont tailRegSeq realSeal tailSeal ∧
                            Cont tailSeal route tailRead ∧
                              PkgSig bundle provenance pkg ∧
                                PkgSig bundle tailRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier windowsDyadicTail tailWindowHandoffRegSeq regSeqRealSealTailSeal
    tailSealRouteRead tailReadPkg
  have tailWindowUnary : UnaryHistory tailWindow :=
    unary_cont_closed carrier.windows_unary carrier.dyadic_unary windowsDyadicTail
  have tailRegSeqUnary : UnaryHistory tailRegSeq :=
    unary_cont_closed tailWindowUnary carrier.handoff_unary tailWindowHandoffRegSeq
  have tailSealUnary : UnaryHistory tailSeal :=
    unary_cont_closed tailRegSeqUnary carrier.realSeal_unary regSeqRealSealTailSeal
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed tailSealUnary carrier.route_unary tailSealRouteRead
  exact
    ⟨carrier.windows_unary, carrier.dyadic_unary, carrier.handoff_unary,
      carrier.realSeal_unary, tailWindowUnary, tailRegSeqUnary, tailSealUnary,
      tailReadUnary, windowsDyadicTail, tailWindowHandoffRegSeq,
      regSeqRealSealTailSeal, tailSealRouteRead, carrier.provenance_pkg, tailReadPkg⟩

end BEDC.Derived.RealWindowBudgetUp
