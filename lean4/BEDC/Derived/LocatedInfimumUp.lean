import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatedInfimumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LocatedInfimumCarrier [AskSetup] [PackageSetup]
    (family lower greatest window regseq realSeal transport route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory family ∧ UnaryHistory lower ∧ UnaryHistory greatest ∧ UnaryHistory window ∧
    UnaryHistory regseq ∧ UnaryHistory realSeal ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        Cont regseq realSeal route ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg

theorem LocatedInfimumLedgerExactness [AskSetup] [PackageSetup]
    {family lower greatest window regseq realSeal transport route provenance name observation :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedInfimumCarrier family lower greatest window regseq realSeal transport route provenance
        name bundle pkg ->
      Cont lower greatest observation ->
        PkgSig bundle observation pkg ->
          UnaryHistory family ∧ UnaryHistory lower ∧ UnaryHistory greatest ∧
            UnaryHistory observation ∧ Cont lower greatest observation ∧
              Cont regseq realSeal route ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle observation pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier lowerGreatestObservation observationPkg
  obtain ⟨familyUnary, lowerUnary, greatestUnary, _windowUnary, regseqUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameUnary,
    regseqRealSealRoute, provenancePkg, _namePkg⟩ := carrier
  have observationUnary : UnaryHistory observation :=
    unary_cont_closed lowerUnary greatestUnary lowerGreatestObservation
  exact
    ⟨familyUnary, lowerUnary, greatestUnary, observationUnary, lowerGreatestObservation,
      regseqRealSealRoute, provenancePkg, observationPkg⟩

end BEDC.Derived.LocatedInfimumUp
