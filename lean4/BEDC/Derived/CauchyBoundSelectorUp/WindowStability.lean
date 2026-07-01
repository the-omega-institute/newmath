import BEDC.Derived.CauchyBoundSelectorUp.NameCertObligations

namespace BEDC.Derived.CauchyBoundSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyBoundSelectorCarrier_window_stability [AskSetup] [PackageSetup]
    {source bound selector transport replay provenance localName selectorRead publicRead
      selectorRead' publicRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory source →
      UnaryHistory bound →
        UnaryHistory selector →
          UnaryHistory transport →
            UnaryHistory replay →
              Cont source bound selectorRead →
                Cont selectorRead replay publicRead →
                  hsame selectorRead selectorRead' →
                    Cont selectorRead' replay publicRead' →
                      PkgSig bundle provenance pkg →
                        PkgSig bundle localName pkg →
                          PkgSig bundle publicRead pkg →
                            PkgSig bundle publicRead' pkg →
                              UnaryHistory selectorRead' ∧ UnaryHistory publicRead' ∧
                                hsame selectorRead selectorRead' ∧
                                  PkgSig bundle publicRead' pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory ProbeBundle Pkg PkgSig
  intro sourceUnary boundUnary _selectorUnary _transportUnary replayUnary selectorRoute
    _publicRoute sameSelector transportedRoute _provenancePkg _localNamePkg _publicPkg
    publicPkg'
  have selectorReadUnary : UnaryHistory selectorRead :=
    unary_cont_closed sourceUnary boundUnary selectorRoute
  have selectorReadUnary' : UnaryHistory selectorRead' :=
    unary_transport selectorReadUnary sameSelector
  have publicReadUnary' : UnaryHistory publicRead' :=
    unary_cont_closed selectorReadUnary' replayUnary transportedRoute
  exact ⟨selectorReadUnary', publicReadUnary', sameSelector, publicPkg'⟩

end BEDC.Derived.CauchyBoundSelectorUp
