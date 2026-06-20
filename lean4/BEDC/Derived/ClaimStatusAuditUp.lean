import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ClaimStatusAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ClaimStatusAuditCarrier [AskSetup] [PackageSetup]
    (expression theoremRow route evidence gap socket admission exportRow transport replay
      provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory expression ∧ UnaryHistory theoremRow ∧ UnaryHistory route ∧
    UnaryHistory evidence ∧ UnaryHistory gap ∧ UnaryHistory socket ∧
      UnaryHistory admission ∧ UnaryHistory exportRow ∧ UnaryHistory transport ∧
        UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

end BEDC.Derived.ClaimStatusAuditUp
