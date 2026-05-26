import BEDC.Derived.MetricCompletionUp.NameCertObligations
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetricCompletionUp.ScopedReadbackScope

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.MetricCompletionUp.NameCertObligations

def MetricCompletionScopedReadbackScope [AskSetup] [PackageSetup]
    (source filterBranch netBranch readback separated transport replay provenance localCert
      scopedRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist hsame UnaryHistory ProbeBundle Pkg
  MetricCompletionCarrier source filterBranch netBranch readback separated transport replay
      provenance localCert bundle pkg ∧
    (hsame scopedRead source ∨ hsame scopedRead filterBranch ∨ hsame scopedRead netBranch ∨
      hsame scopedRead readback ∨ hsame scopedRead separated ∨ hsame scopedRead transport ∨
        hsame scopedRead replay ∨ hsame scopedRead provenance ∨ hsame scopedRead localCert) ∧
      UnaryHistory scopedRead

end BEDC.Derived.MetricCompletionUp.ScopedReadbackScope
