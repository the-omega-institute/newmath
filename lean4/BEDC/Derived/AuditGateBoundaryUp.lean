import BEDC.FKernel.Hist

namespace BEDC.Derived.AuditGateBoundaryUp

open BEDC.FKernel.Hist

inductive AuditGateBoundaryUp : Type where
  | mk
      (sourceScan dependencyReport targetAudit originLedger transport continuation provenance gap name :
        BHist) :
      AuditGateBoundaryUp

end BEDC.Derived.AuditGateBoundaryUp
