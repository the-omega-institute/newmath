import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive SubjectReductionRouteAuditUp : Type where
  | mk
      (bundle exactness invocation handoff socket transport replay provenance localName :
        BHist) : SubjectReductionRouteAuditUp
deriving DecidableEq

end BEDC.Derived
