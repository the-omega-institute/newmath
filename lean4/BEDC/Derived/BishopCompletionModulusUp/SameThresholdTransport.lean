import BEDC.Derived.BishopCompletionModulusUp.TasteGate

namespace BEDC.Derived.BishopCompletionModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopCompletionModulusCarrier_same_threshold_transport [AskSetup] [PackageSetup]
    {M S n k W D R E H C P N M' S' n' k' W' D' R' E' H' C' P' N'
      kRead WRead RRead sealRead kRead' WRead' RRead' sealRead' : BHist}
    {bundle bundle' : ProbeBundle ProbeName} {pkg pkg' : Pkg} :
    BishopCompletionModulusCarrier M S n k W D R E H C P N bundle pkg ->
      BishopCompletionModulusCarrier M' S' n' k' W' D' R' E' H' C' P' N'
        bundle' pkg' ->
        hsame M M' ->
          hsame S S' ->
            hsame n n' ->
              hsame D D' ->
                hsame E E' ->
                  Cont M n kRead ->
                    Cont S kRead WRead ->
                      Cont WRead D RRead ->
                        Cont RRead E sealRead ->
                          Cont M' n' kRead' ->
                            Cont S' kRead' WRead' ->
                              Cont WRead' D' RRead' ->
                                Cont RRead' E' sealRead' ->
                                  hsame kRead kRead' ∧ hsame WRead WRead' ∧
                                    hsame RRead RRead' ∧ hsame sealRead sealRead' ∧
                                      UnaryHistory sealRead ∧ UnaryHistory sealRead' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier carrier' sameM sameS sameN sameD sameE routeK routeW routeR routeSeal
    routeK' routeW' routeR' routeSeal'
  obtain ⟨unaryM, unaryS, unaryN, _unaryK, _unaryW, unaryD, _unaryR, unaryE,
    _unaryH, _unaryC, _unaryP, _unaryLocalName, _modulusRoute, _windowRoute,
      _regularRoute, _sealRoute, _provenancePkg, _localNamePkg⟩ := carrier
  obtain ⟨unaryM', unaryS', unaryN', _unaryK', _unaryW', unaryD', _unaryR',
    unaryE', _unaryH', _unaryC', _unaryP', _unaryLocalName', _modulusRoute',
      _windowRoute', _regularRoute', _sealRoute', _provenancePkg',
        _localNamePkg'⟩ := carrier'
  have sameKRead : hsame kRead kRead' :=
    cont_respects_hsame sameM sameN routeK routeK'
  have sameWRead : hsame WRead WRead' :=
    cont_respects_hsame sameS sameKRead routeW routeW'
  have sameRRead : hsame RRead RRead' :=
    cont_respects_hsame sameWRead sameD routeR routeR'
  have sameSealRead : hsame sealRead sealRead' :=
    cont_respects_hsame sameRRead sameE routeSeal routeSeal'
  have kReadUnary : UnaryHistory kRead :=
    unary_cont_closed unaryM unaryN routeK
  have wReadUnary : UnaryHistory WRead :=
    unary_cont_closed unaryS kReadUnary routeW
  have rReadUnary : UnaryHistory RRead :=
    unary_cont_closed wReadUnary unaryD routeR
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed rReadUnary unaryE routeSeal
  have kReadUnary' : UnaryHistory kRead' :=
    unary_cont_closed unaryM' unaryN' routeK'
  have wReadUnary' : UnaryHistory WRead' :=
    unary_cont_closed unaryS' kReadUnary' routeW'
  have rReadUnary' : UnaryHistory RRead' :=
    unary_cont_closed wReadUnary' unaryD' routeR'
  have sealReadUnary' : UnaryHistory sealRead' :=
    unary_cont_closed rReadUnary' unaryE' routeSeal'
  exact
    ⟨sameKRead, sameWRead, sameRRead, sameSealRead, sealReadUnary,
      sealReadUnary'⟩

end BEDC.Derived.BishopCompletionModulusUp
