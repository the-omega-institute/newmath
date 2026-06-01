import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ClosedBoundedIntervalConstructiveSource [AskSetup] [PackageSetup]
    (lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory order ∧ UnaryHistory rational ∧
    UnaryHistory dyadic ∧ UnaryHistory stream ∧ UnaryHistory readback ∧
      UnaryHistory sealRow ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory localName ∧ Cont lower upper order ∧
          Cont order rational dyadic ∧ Cont stream readback sealRow ∧
            Cont transport replay provenance ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localName pkg

end BEDC.Derived.ClosedboundedintervalUp
