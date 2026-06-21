import BEDC.Derived.PhysicalLawBridgeUp.NameCertSurface

namespace BEDC.Derived.PhysicalLawBridgeUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem PhysicalLawBridgeLawGapNonescape
    {law empirical bridge object fit failure transport replay provenance name nameRead : BHist} :
    PhysicalLawBridgeCarrier law empirical bridge object fit failure transport replay provenance
        name →
      Cont replay provenance nameRead →
        hsame nameRead name →
          UnaryHistory law ∧ UnaryHistory empirical ∧ UnaryHistory bridge ∧
            UnaryHistory object ∧ UnaryHistory fit ∧ UnaryHistory failure ∧
              Cont law empirical bridge ∧ Cont object fit failure ∧
                Cont replay provenance nameRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory PhysicalLawBridgeCarrier
  intro carrier replayProvenanceName _sameName
  obtain ⟨lawUnary, empiricalUnary, bridgeUnary, objectUnary, fitUnary, failureUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, lawEmpiricalBridge,
    objectFitFailure, _transportReplayProvenance⟩ := carrier
  exact
    ⟨lawUnary, empiricalUnary, bridgeUnary, objectUnary, fitUnary, failureUnary,
      lawEmpiricalBridge, objectFitFailure, replayProvenanceName⟩

end BEDC.Derived.PhysicalLawBridgeUp
