import BEDC.Derived.CoveringdimensionUp.FiniteRefinementNameCert

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionFiniteOrderHandoff [AskSetup] [PackageSetup]
    {K E C R O L S M A G H T P N orderRead namedRead nerveRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionFiniteRefinementCarrier K E C R O L S M A G H T P N bundle pkg →
      Cont O L orderRead →
        Cont orderRead T namedRead →
          Cont S orderRead nerveRead →
            Cont namedRead M completionRead →
              PkgSig bundle namedRead pkg →
                PkgSig bundle nerveRead pkg →
                  PkgSig bundle completionRead pkg →
                    UnaryHistory O ∧ UnaryHistory L ∧ UnaryHistory S ∧ UnaryHistory M ∧
                      UnaryHistory orderRead ∧ UnaryHistory namedRead ∧
                        UnaryHistory nerveRead ∧ UnaryHistory completionRead ∧
                          Cont O L orderRead ∧ Cont orderRead T namedRead ∧
                            Cont S orderRead nerveRead ∧
                              Cont namedRead M completionRead ∧ PkgSig bundle P pkg ∧
                                PkgSig bundle namedRead pkg ∧ PkgSig bundle nerveRead pkg ∧
                                  PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier orderRoute namedRoute nerveRoute completionRoute namedPkg nervePkg
    completionPkg
  obtain ⟨_KUnary, _EUnary, _CUnary, _RUnary, OUnary, LUnary, SUnary, MUnary,
    _AUnary, _GUnary, _HUnary, TUnary, _PUnary, _NUnary, _KELedger, _CROrder,
    _OLTReplay, _SMAWindow, _AGTransport, _HTProvenance, provenancePkg, _namePkg⟩ :=
      carrier
  have orderUnary : UnaryHistory orderRead :=
    unary_cont_closed OUnary LUnary orderRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed orderUnary TUnary namedRoute
  have nerveUnary : UnaryHistory nerveRead :=
    unary_cont_closed SUnary orderUnary nerveRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed namedUnary MUnary completionRoute
  exact
    ⟨OUnary, LUnary, SUnary, MUnary, orderUnary, namedUnary, nerveUnary,
      completionUnary, orderRoute, namedRoute, nerveRoute, completionRoute, provenancePkg,
      namedPkg, nervePkg, completionPkg⟩

end BEDC.Derived.CoveringdimensionUp
