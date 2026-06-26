import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.KelleyficationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def KelleyficationCarrier [AskSetup] [PackageSetup]
    (topology coreCompact compactOpen window transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory topology ∧ UnaryHistory coreCompact ∧ UnaryHistory compactOpen ∧
    UnaryHistory window ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
      UnaryHistory provenance ∧ UnaryHistory localName ∧
        Cont topology coreCompact compactOpen ∧ PkgSig bundle provenance pkg ∧
          PkgSig bundle localName pkg

theorem KelleyficationCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {topology coreCompact compactOpen window transport replay provenance localName reflected
      exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KelleyficationCarrier topology coreCompact compactOpen window transport replay provenance
        localName bundle pkg →
      Cont compactOpen window reflected →
        Cont reflected replay exported →
          PkgSig bundle exported pkg →
            UnaryHistory topology ∧ UnaryHistory coreCompact ∧ UnaryHistory compactOpen ∧
              UnaryHistory window ∧ UnaryHistory reflected ∧ UnaryHistory exported ∧
                Cont topology coreCompact compactOpen ∧ Cont compactOpen window reflected ∧
                  Cont reflected replay exported ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle exported pkg ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier reflectedRoute exportedRoute exportedPkg
  obtain ⟨topologyUnary, coreCompactUnary, compactOpenUnary, windowUnary, _transportUnary,
    replayUnary, _provenanceUnary, _localNameUnary, compactOpenRoute, provenancePkg,
    localNamePkg⟩ := carrier
  have reflectedUnary : UnaryHistory reflected :=
    unary_cont_closed compactOpenUnary windowUnary reflectedRoute
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed reflectedUnary replayUnary exportedRoute
  exact
    ⟨topologyUnary, coreCompactUnary, compactOpenUnary, windowUnary, reflectedUnary,
      exportedUnary, compactOpenRoute, reflectedRoute, exportedRoute, provenancePkg,
      exportedPkg, localNamePkg⟩

end BEDC.Derived.KelleyficationUp
