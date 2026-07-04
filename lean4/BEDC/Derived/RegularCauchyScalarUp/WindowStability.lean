import BEDC.Derived.RegularCauchyScalarUp.RealHandoff

namespace BEDC.Derived.RegularCauchyScalarUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyScalarCarrier_window_stability [AskSetup] [PackageSetup]
    {X A W D F E H C P N X' A' W' D' F' E' H' C' P' N' sourceRead sourceRead'
      scaledRead scaledRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyScalarCarrier X A W D F E H C P N bundle pkg ->
      RegularCauchyScalarCarrier X' A' W' D' F' E' H' C' P' N' bundle pkg ->
        hsame X X' ->
          hsame A A' ->
            hsame W W' ->
              hsame D D' ->
                hsame F F' ->
                  hsame E E' ->
                    hsame H H' ->
                      hsame C C' ->
                        hsame P P' ->
                          hsame N N' ->
                            Cont X W sourceRead ->
                              Cont X' W' sourceRead' ->
                                Cont sourceRead F scaledRead ->
                                  Cont sourceRead' F' scaledRead' ->
                                    hsame sourceRead sourceRead' ∧
                                      hsame scaledRead scaledRead' ∧
                                        UnaryHistory sourceRead ∧
                                          UnaryHistory sourceRead' ∧
                                            UnaryHistory scaledRead ∧
                                              UnaryHistory scaledRead' := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier carrier' sameX _sameA sameW _sameD sameF _sameE _sameH _sameC _sameP
    _sameN sourceRoute sourceRoute' scaledRoute scaledRoute'
  obtain ⟨unaryX, _unaryA, unaryW, _unaryD, unaryF, _unaryE, _unaryH, _unaryC,
    _unaryP, _unaryN, _storedSourceRoute, _storedScaledRoute, _storedRealRoute,
    _sameTransport, _provenancePkg⟩ := carrier
  obtain ⟨unaryX', _unaryA', unaryW', _unaryD', unaryF', _unaryE', _unaryH',
    _unaryC', _unaryP', _unaryN', _storedSourceRoute', _storedScaledRoute',
    _storedRealRoute', _sameTransport', _provenancePkg'⟩ := carrier'
  have sameSourceRead : hsame sourceRead sourceRead' :=
    cont_respects_hsame sameX sameW sourceRoute sourceRoute'
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryX unaryW sourceRoute
  have sourceReadUnary' : UnaryHistory sourceRead' :=
    unary_cont_closed unaryX' unaryW' sourceRoute'
  have sameScaledRead : hsame scaledRead scaledRead' :=
    cont_respects_hsame sameSourceRead sameF scaledRoute scaledRoute'
  have scaledReadUnary : UnaryHistory scaledRead :=
    unary_cont_closed sourceReadUnary unaryF scaledRoute
  have scaledReadUnary' : UnaryHistory scaledRead' :=
    unary_cont_closed sourceReadUnary' unaryF' scaledRoute'
  exact
    ⟨sameSourceRead, sameScaledRead, sourceReadUnary, sourceReadUnary',
      scaledReadUnary, scaledReadUnary'⟩

end BEDC.Derived.RegularCauchyScalarUp
