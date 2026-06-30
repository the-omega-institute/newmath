import BEDC.Derived.SubdifferentialUp.TasteGate

namespace BEDC.Derived.SubdifferentialUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SubdifferentialSupportInequalityExactness [AskSetup] [PackageSetup]
    {functional point covector pairing support epigraph cone transport replay provenance name
      supportRead stationarityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubdifferentialCarrier functional point covector pairing support epigraph cone transport
        replay provenance name bundle pkg →
      Cont pairing support supportRead →
        Cont support cone stationarityRead →
          UnaryHistory supportRead ∧ Cont pairing support supportRead ∧
            UnaryHistory stationarityRead ∧ Cont support cone stationarityRead ∧
              PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier supportRoute stationarityRoute
  obtain ⟨_functionalUnary, _pointUnary, _covectorUnary, pairingUnary, supportUnary,
    _epigraphUnary, coneUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _nameUnary, _epigraphRoute, _replayRoute, provenancePkg⟩ := carrier
  have supportReadUnary : UnaryHistory supportRead :=
    unary_cont_closed pairingUnary supportUnary supportRoute
  have stationarityReadUnary : UnaryHistory stationarityRead :=
    unary_cont_closed supportUnary coneUnary stationarityRoute
  exact
    ⟨supportReadUnary, supportRoute, stationarityReadUnary, stationarityRoute, provenancePkg⟩

end BEDC.Derived.SubdifferentialUp
