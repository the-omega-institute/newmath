import BEDC.Derived.CauchySequenceSpaceUp

namespace BEDC.Derived.CauchySequenceSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchySequenceSpaceRealLimitUniquenessSealPublicConsumer [AskSetup] [PackageSetup]
    {family0 schedule0 window0 tolerance0 completion0 transport0 route0 name0 family1
      schedule1 window1 tolerance1 completion1 transport1 route1 name1 comparison seal0 seal1
      uniquenessRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceSpaceCarrier family0 schedule0 window0 tolerance0 completion0 transport0
        route0 name0 bundle pkg →
      CauchySequenceSpaceCarrier family1 schedule1 window1 tolerance1 completion1 transport1
        route1 name1 bundle pkg →
        hsame family0 family1 →
          hsame schedule0 schedule1 →
            hsame tolerance0 tolerance1 →
              UnaryHistory comparison →
                Cont completion0 comparison seal0 →
                  Cont completion1 comparison seal1 →
                    Cont seal0 seal1 uniquenessRead →
                      PkgSig bundle uniquenessRead pkg →
                        UnaryHistory family0 ∧ UnaryHistory family1 ∧
                          UnaryHistory schedule0 ∧ UnaryHistory schedule1 ∧
                            UnaryHistory tolerance0 ∧ UnaryHistory tolerance1 ∧
                              UnaryHistory completion0 ∧ UnaryHistory completion1 ∧
                                UnaryHistory comparison ∧ UnaryHistory seal0 ∧
                                  UnaryHistory seal1 ∧ UnaryHistory uniquenessRead ∧
                                    hsame family0 family1 ∧ hsame schedule0 schedule1 ∧
                                      hsame tolerance0 tolerance1 ∧
                                        Cont completion0 comparison seal0 ∧
                                          Cont completion1 comparison seal1 ∧
                                            Cont seal0 seal1 uniquenessRead ∧
                                              PkgSig bundle route0 pkg ∧
                                                PkgSig bundle route1 pkg ∧
                                                  PkgSig bundle uniquenessRead pkg := by
  -- BEDC touchpoint anchor: CauchySequenceSpaceCarrier BHist ProbeBundle Pkg hsame Cont PkgSig UnaryHistory
  intro carrier0 carrier1 sameFamily sameSchedule sameTolerance comparisonUnary completion0Seal
    completion1Seal sealUniqueness uniquenessPkg
  obtain ⟨familyUnary0, scheduleUnary0, _windowUnary0, toleranceUnary0, completionUnary0,
    _transportUnary0, _routeUnary0, _nameUnary0, _familyScheduleWindow0,
    _windowToleranceCompletion0, _completionTransportRoute0, routePkg0, _namePkg0⟩ :=
    carrier0
  obtain ⟨familyUnary1, scheduleUnary1, _windowUnary1, toleranceUnary1, completionUnary1,
    _transportUnary1, _routeUnary1, _nameUnary1, _familyScheduleWindow1,
    _windowToleranceCompletion1, _completionTransportRoute1, routePkg1, _namePkg1⟩ :=
    carrier1
  have sealUnary0 : UnaryHistory seal0 :=
    unary_cont_closed completionUnary0 comparisonUnary completion0Seal
  have sealUnary1 : UnaryHistory seal1 :=
    unary_cont_closed completionUnary1 comparisonUnary completion1Seal
  have uniquenessUnary : UnaryHistory uniquenessRead :=
    unary_cont_closed sealUnary0 sealUnary1 sealUniqueness
  exact
    ⟨familyUnary0, familyUnary1, scheduleUnary0, scheduleUnary1, toleranceUnary0,
      toleranceUnary1, completionUnary0, completionUnary1, comparisonUnary, sealUnary0,
      sealUnary1, uniquenessUnary, sameFamily, sameSchedule, sameTolerance, completion0Seal,
      completion1Seal, sealUniqueness, routePkg0, routePkg1, uniquenessPkg⟩

end BEDC.Derived.CauchySequenceSpaceUp
