import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BishopRealNameRealizerUp [AskSetup] [PackageSetup]
    (sourceWindow streamWindow dyadicLedger regSeqReadback locatedWitness realSeal transport replay
      provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory sourceWindow /\
    UnaryHistory streamWindow /\
      UnaryHistory dyadicLedger /\
        UnaryHistory regSeqReadback /\
          UnaryHistory locatedWitness /\
            UnaryHistory realSeal /\
              UnaryHistory transport /\
                UnaryHistory replay /\
                  UnaryHistory provenance /\
                    UnaryHistory localName /\
                      Cont sourceWindow streamWindow dyadicLedger /\
                        Cont dyadicLedger regSeqReadback locatedWitness /\
                          Cont locatedWitness realSeal replay /\
                            PkgSig bundle provenance pkg /\
                              PkgSig bundle localName pkg

end BEDC.Derived
