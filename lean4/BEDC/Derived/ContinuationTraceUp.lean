import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.ContinuationTraceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

structure ContinuationTraceCarrier [AskSetup] [PackageSetup] where
  source : BHist
  markTail : BHist
  target : BHist
  traceLedger : BHist
  transport : BHist
  continuation : BHist
  provenance : Pkg
  name : NameCert (fun row : BHist => hsame row target) hsame
  route_witness : Cont source markTail target
  source_transport : hsame source source
  target_transport : hsame target target

end BEDC.Derived.ContinuationTraceUp
