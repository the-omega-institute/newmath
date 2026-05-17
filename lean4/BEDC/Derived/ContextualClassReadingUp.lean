import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ContextualClassReadingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ContextualClassReadingCarrier [AskSetup] [PackageSetup]
    (expression context relation scope transport route provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory expression ∧ UnaryHistory context ∧ UnaryHistory relation ∧
    UnaryHistory scope ∧ UnaryHistory transport ∧ UnaryHistory route ∧
      UnaryHistory provenance ∧ UnaryHistory localName ∧
        Cont expression context relation ∧ Cont relation scope route ∧
          Cont route transport provenance ∧ PkgSig bundle localName pkg

theorem ContextualClassReadingCarrier_classifier_transport [AskSetup] [PackageSetup]
    {expression context relation scope transport route provenance localName transported replay : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContextualClassReadingCarrier expression context relation scope transport route provenance
        localName bundle pkg →
      Cont context relation transported →
        Cont transported scope replay →
          PkgSig bundle replay pkg →
            UnaryHistory context ∧ UnaryHistory relation ∧ UnaryHistory transported ∧
              UnaryHistory replay ∧ Cont context relation transported ∧
                Cont transported scope replay ∧ PkgSig bundle replay pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier contextRelation transportedScope replayPkg
  obtain ⟨_expressionUnary, contextUnary, relationUnary, scopeUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _localNameUnary, _expressionContextRelation,
    _relationScopeRoute, _routeTransportProvenance, _localNamePkg⟩ := carrier
  have transportedUnary : UnaryHistory transported :=
    unary_cont_closed contextUnary relationUnary contextRelation
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed transportedUnary scopeUnary transportedScope
  exact
    ⟨contextUnary, relationUnary, transportedUnary, replayUnary, contextRelation,
      transportedScope, replayPkg⟩

theorem ContextualClassReadingCarrier_no_object_promotion [AskSetup] [PackageSetup]
    {expression context relation scope transport route provenance localName objectRead hostTail :
      BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContextualClassReadingCarrier expression context relation scope transport route provenance
        localName bundle pkg ->
      Cont context relation objectRead ->
        PkgSig bundle objectRead pkg ->
          UnaryHistory context ∧ UnaryHistory relation ∧ UnaryHistory objectRead ∧
            Cont context relation objectRead ∧ PkgSig bundle localName pkg ∧
              PkgSig bundle objectRead pkg ∧
                (Cont objectRead (BHist.e0 hostTail) context -> False) ∧
                  (Cont objectRead (BHist.e1 hostTail) context -> False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier contextRelation objectReadPkg
  obtain ⟨_expressionUnary, contextUnary, relationUnary, _scopeUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _localNameUnary, _expressionContextRelation,
    _relationScopeRoute, _routeTransportProvenance, localNamePkg⟩ := carrier
  have objectReadUnary : UnaryHistory objectRead :=
    unary_cont_closed contextUnary relationUnary contextRelation
  exact
    ⟨contextUnary, relationUnary, objectReadUnary, contextRelation, localNamePkg,
      objectReadPkg,
      (fun back =>
        (cont_mutual_extension_right_tail_absurd.left contextRelation back)),
      (fun back =>
        (cont_mutual_extension_right_tail_absurd.right contextRelation back))⟩

theorem ContextualClassReadingLedgerExactness [AskSetup] [PackageSetup]
    {expression context relation scope transport route provenance localName transported replay : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContextualClassReadingCarrier expression context relation scope transport route provenance
        localName bundle pkg →
      Cont context relation transported →
        Cont transported scope replay →
          PkgSig bundle replay pkg →
            UnaryHistory expression ∧ UnaryHistory context ∧ UnaryHistory relation ∧
              UnaryHistory scope ∧ UnaryHistory transported ∧ UnaryHistory replay ∧
                Cont expression context relation ∧ Cont relation scope route ∧
                  Cont context relation transported ∧ Cont transported scope replay ∧
                    PkgSig bundle localName pkg ∧ PkgSig bundle replay pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier contextRelation transportedScope replayPkg
  obtain ⟨expressionUnary, contextUnary, relationUnary, scopeUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _localNameUnary, expressionContextRelation,
    relationScopeRoute, _routeTransportProvenance, localNamePkg⟩ := carrier
  have transportedUnary : UnaryHistory transported :=
    unary_cont_closed contextUnary relationUnary contextRelation
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed transportedUnary scopeUnary transportedScope
  exact
    ⟨expressionUnary, contextUnary, relationUnary, scopeUnary, transportedUnary,
      replayUnary, expressionContextRelation, relationScopeRoute, contextRelation,
      transportedScope, localNamePkg, replayPkg⟩

end BEDC.Derived.ContextualClassReadingUp
