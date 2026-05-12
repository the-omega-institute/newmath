import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteWindowEnvelopeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FiniteWindowEnvelopeCarrier [AskSetup] [PackageSetup]
    (source anchor window ledger streamSeal regSeal endpoint provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory anchor ∧ UnaryHistory window ∧ UnaryHistory ledger ∧
    Cont window ledger regSeal ∧ Cont regSeal endpoint streamSeal ∧
      Cont streamSeal localCert provenance ∧ PkgSig bundle provenance pkg

theorem FiniteWindowEnvelopeCarrier_regseqrat_seal_handoff [AskSetup] [PackageSetup]
    {source anchor window ledger streamSeal regSeal endpoint provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteWindowEnvelopeCarrier source anchor window ledger streamSeal regSeal endpoint provenance
        localCert bundle pkg →
      UnaryHistory regSeal ∧ hsame regSeal (append window ledger) ∧
        PkgSig bundle provenance pkg := by
  intro carrier
  have windowUnary : UnaryHistory window :=
    carrier.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    carrier.right.right.right.left
  have regSealCont : Cont window ledger regSeal :=
    carrier.right.right.right.right.left
  have regSealUnary : UnaryHistory regSeal :=
    unary_cont_closed windowUnary ledgerUnary regSealCont
  have regSealSame : hsame regSeal (append window ledger) :=
    regSealCont
  exact And.intro regSealUnary (And.intro regSealSame carrier.right.right.right.right.right.right.right)

end BEDC.Derived.FiniteWindowEnvelopeUp
