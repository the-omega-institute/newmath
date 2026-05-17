import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ClosedObservationSystemUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ClosedObservationSystemCarrier [AskSetup] [PackageSetup]
    (observation record conservation transport continuation provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory observation ∧ UnaryHistory record ∧ UnaryHistory transport ∧
    UnaryHistory continuation ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
      Cont observation record conservation ∧
        hsame transport (append observation record) ∧ PkgSig bundle provenance pkg

theorem ClosedObservationSystemNameCertObligations [AskSetup] [PackageSetup]
    {observation record conservation transport continuation provenance localName gapRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedObservationSystemCarrier observation record conservation transport continuation
        provenance localName bundle pkg ->
      Cont continuation provenance gapRead ->
        PkgSig bundle gapRead pkg ->
          UnaryHistory observation ∧ UnaryHistory record ∧ UnaryHistory conservation ∧
            UnaryHistory gapRead ∧ Cont observation record conservation ∧
              Cont continuation provenance gapRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle gapRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig hsame
  intro carrier gapRoute gapPkg
  obtain ⟨observationUnary, recordUnary, _transportUnary, continuationUnary, provenanceUnary,
    _localNameUnary, observationRecordConservation, _transportSame, provenancePkg⟩ := carrier
  have conservationUnary : UnaryHistory conservation :=
    unary_cont_closed observationUnary recordUnary observationRecordConservation
  have gapUnary : UnaryHistory gapRead :=
    unary_cont_closed continuationUnary provenanceUnary gapRoute
  exact
    ⟨observationUnary, recordUnary, conservationUnary, gapUnary,
      observationRecordConservation, gapRoute, provenancePkg, gapPkg⟩

end BEDC.Derived.ClosedObservationSystemUp
