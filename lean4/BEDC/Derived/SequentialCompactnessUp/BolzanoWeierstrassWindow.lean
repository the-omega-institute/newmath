import BEDC.Derived.SequentialCompactnessUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SequentialCompactnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialCompactnessBolzanoWeierstrassWindow [AskSetup] [PackageSetup]
    {compactSource sequenceWindow selectorWindow readback realSeal boundedSource clusterSeal
      finalSeal provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory compactSource →
      UnaryHistory sequenceWindow →
        UnaryHistory readback →
          UnaryHistory boundedSource →
            UnaryHistory provenance →
              Cont compactSource sequenceWindow selectorWindow →
                Cont selectorWindow readback realSeal →
                  Cont realSeal boundedSource clusterSeal →
                    Cont clusterSeal provenance finalSeal →
                      PkgSig bundle provenance pkg →
                        PkgSig bundle finalSeal pkg →
                          UnaryHistory selectorWindow ∧
                            UnaryHistory realSeal ∧
                              UnaryHistory clusterSeal ∧
                                UnaryHistory finalSeal ∧
                                  Cont compactSource sequenceWindow selectorWindow ∧
                                    Cont selectorWindow readback realSeal ∧
                                      Cont realSeal boundedSource clusterSeal ∧
                                        Cont clusterSeal provenance finalSeal ∧
                                          PkgSig bundle finalSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro compactUnary sequenceUnary readbackUnary boundedUnary provenanceUnary selectorRoute
    realSealRoute clusterRoute finalRoute _provenancePkg finalPkg
  have selectorUnary : UnaryHistory selectorWindow :=
    unary_cont_closed compactUnary sequenceUnary selectorRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed selectorUnary readbackUnary realSealRoute
  have clusterUnary : UnaryHistory clusterSeal :=
    unary_cont_closed realSealUnary boundedUnary clusterRoute
  have finalUnary : UnaryHistory finalSeal :=
    unary_cont_closed clusterUnary provenanceUnary finalRoute
  exact
    ⟨selectorUnary, realSealUnary, clusterUnary, finalUnary, selectorRoute, realSealRoute,
      clusterRoute, finalRoute, finalPkg⟩

end BEDC.Derived.SequentialCompactnessUp
