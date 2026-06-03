import BEDC.Derived.WeakTopologyUp.NamecertObligations

namespace BEDC.Derived.WeakTopologyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem WeakTopologyFunctionalWindowStability [AskSetup] [PackageSetup]
    {source functionals neighborhood testWindow scalar transport replay provenance localName
      subwindowRead scalarRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory source →
      UnaryHistory functionals →
        UnaryHistory neighborhood →
          UnaryHistory testWindow →
            UnaryHistory scalar →
              UnaryHistory transport →
                UnaryHistory replay →
                  UnaryHistory provenance →
                    UnaryHistory localName →
                      Cont testWindow functionals subwindowRead →
                        Cont subwindowRead neighborhood scalarRead →
                          Cont scalarRead localName namedRead →
                            PkgSig bundle provenance pkg →
                              PkgSig bundle localName pkg →
                                PkgSig bundle namedRead pkg →
                                  UnaryHistory source ∧ UnaryHistory functionals ∧
                                    UnaryHistory neighborhood ∧ UnaryHistory testWindow ∧
                                      UnaryHistory scalar ∧ UnaryHistory subwindowRead ∧
                                        UnaryHistory scalarRead ∧ UnaryHistory namedRead ∧
                                          Cont testWindow functionals subwindowRead ∧
                                            Cont subwindowRead neighborhood scalarRead ∧
                                              Cont scalarRead localName namedRead ∧
                                                PkgSig bundle provenance pkg ∧
                                                  PkgSig bundle localName pkg ∧
                                                    PkgSig bundle namedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro sourceUnary functionalsUnary neighborhoodUnary testWindowUnary scalarUnary
    _transportUnary _replayUnary _provenanceUnary localNameUnary subwindowRoute scalarRoute
    namedRoute provenancePkg localNamePkg namedPkg
  have subwindowUnary : UnaryHistory subwindowRead :=
    unary_cont_closed testWindowUnary functionalsUnary subwindowRoute
  have scalarReadUnary : UnaryHistory scalarRead :=
    unary_cont_closed subwindowUnary neighborhoodUnary scalarRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed scalarReadUnary localNameUnary namedRoute
  exact
    ⟨sourceUnary, functionalsUnary, neighborhoodUnary, testWindowUnary, scalarUnary,
      subwindowUnary, scalarReadUnary, namedReadUnary, subwindowRoute, scalarRoute,
      namedRoute, provenancePkg, localNamePkg, namedPkg⟩

end BEDC.Derived.WeakTopologyUp
