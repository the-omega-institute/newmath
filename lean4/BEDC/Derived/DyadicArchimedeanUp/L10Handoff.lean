import BEDC.Derived.DyadicArchimedeanUp.NameCertObligations

namespace BEDC.Derived.DyadicArchimedeanUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicArchimedeanCarrier [AskSetup] [PackageSetup]
    (source bound scale replay comparison enclosure transport route provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory bound ∧ UnaryHistory scale ∧ UnaryHistory replay ∧
    UnaryHistory comparison ∧ UnaryHistory enclosure ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory localCert ∧ PkgSig bundle provenance pkg

theorem DyadicArchimedeanCarrier_l10_handoff [AskSetup] [PackageSetup]
    {source bound scale replay comparison enclosure transport route provenance localCert
      scaleRead comparisonRead enclosureRead l10Read : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicArchimedeanCarrier source bound scale replay comparison enclosure transport route
        provenance localCert bundle pkg ->
      Cont source scale scaleRead ->
        Cont scaleRead replay comparisonRead ->
          Cont comparisonRead enclosure enclosureRead ->
            Cont enclosureRead route l10Read ->
              PkgSig bundle l10Read pkg ->
                UnaryHistory source ∧ UnaryHistory bound ∧ UnaryHistory scale ∧
                  UnaryHistory replay ∧ UnaryHistory comparison ∧ UnaryHistory enclosure ∧
                    UnaryHistory scaleRead ∧ UnaryHistory comparisonRead ∧
                      UnaryHistory enclosureRead ∧ UnaryHistory l10Read ∧
                        Cont source scale scaleRead ∧
                          Cont scaleRead replay comparisonRead ∧
                            Cont comparisonRead enclosure enclosureRead ∧
                              Cont enclosureRead route l10Read ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle l10Read pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier scaleRoute comparisonRoute enclosureRoute l10Route l10Pkg
  obtain
    ⟨sourceUnary, boundUnary, scaleUnary, replayUnary, comparisonUnary, enclosureUnary,
      _transportUnary, routeUnary, _localCertUnary, provenancePkg⟩ := carrier
  have scaleReadUnary : UnaryHistory scaleRead :=
    unary_cont_closed sourceUnary scaleUnary scaleRoute
  have comparisonReadUnary : UnaryHistory comparisonRead :=
    unary_cont_closed scaleReadUnary replayUnary comparisonRoute
  have enclosureReadUnary : UnaryHistory enclosureRead :=
    unary_cont_closed comparisonReadUnary enclosureUnary enclosureRoute
  have l10ReadUnary : UnaryHistory l10Read :=
    unary_cont_closed enclosureReadUnary routeUnary l10Route
  exact
    ⟨sourceUnary, boundUnary, scaleUnary, replayUnary, comparisonUnary, enclosureUnary,
      scaleReadUnary, comparisonReadUnary, enclosureReadUnary, l10ReadUnary, scaleRoute,
      comparisonRoute, enclosureRoute, l10Route, provenancePkg, l10Pkg⟩

end BEDC.Derived.DyadicArchimedeanUp
