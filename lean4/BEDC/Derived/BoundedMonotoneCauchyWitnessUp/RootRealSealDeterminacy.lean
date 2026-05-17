import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_root_real_seal_determinacy
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      windowA windowB modulusA modulusB trapA trapB realA realB : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule windowA →
        Cont source schedule windowB →
          Cont windowA witness modulusA →
            Cont windowB witness modulusB →
              Cont modulusA trap trapA →
                Cont modulusB trap trapB →
                  Cont trapA sealRow realA →
                    Cont trapB sealRow realB →
                      PkgSig bundle realA pkg →
                        PkgSig bundle realB pkg →
                          UnaryHistory windowA ∧ UnaryHistory windowB ∧
                            UnaryHistory modulusA ∧ UnaryHistory modulusB ∧
                              UnaryHistory trapA ∧ UnaryHistory trapB ∧ UnaryHistory realA ∧
                                UnaryHistory realB ∧ hsame windowA windowB ∧
                                  hsame modulusA modulusB ∧ hsame trapA trapB ∧
                                    hsame realA realB ∧ PkgSig bundle realA pkg ∧
                                      PkgSig bundle realB pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sourceScheduleWindowA sourceScheduleWindowB windowWitnessModulusA
    windowWitnessModulusB modulusTrapA modulusTrapB trapSealRealA trapSealRealB realPkgA
    realPkgB
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, witnessUnary, _ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, _provenancePkg⟩ := carrier
  have windowUnaryA : UnaryHistory windowA :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleWindowA
  have windowUnaryB : UnaryHistory windowB :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleWindowB
  have modulusUnaryA : UnaryHistory modulusA :=
    unary_cont_closed windowUnaryA witnessUnary windowWitnessModulusA
  have modulusUnaryB : UnaryHistory modulusB :=
    unary_cont_closed windowUnaryB witnessUnary windowWitnessModulusB
  have trapUnaryA : UnaryHistory trapA :=
    unary_cont_closed modulusUnaryA trapUnary modulusTrapA
  have trapUnaryB : UnaryHistory trapB :=
    unary_cont_closed modulusUnaryB trapUnary modulusTrapB
  have realUnaryA : UnaryHistory realA :=
    unary_cont_closed trapUnaryA sealUnary trapSealRealA
  have realUnaryB : UnaryHistory realB :=
    unary_cont_closed trapUnaryB sealUnary trapSealRealB
  have sameWindow : hsame windowA windowB :=
    cont_respects_hsame (hsame_refl source) (hsame_refl schedule) sourceScheduleWindowA
      sourceScheduleWindowB
  have sameModulus : hsame modulusA modulusB :=
    cont_respects_hsame sameWindow (hsame_refl witness) windowWitnessModulusA
      windowWitnessModulusB
  have sameTrap : hsame trapA trapB :=
    cont_respects_hsame sameModulus (hsame_refl trap) modulusTrapA modulusTrapB
  have sameReal : hsame realA realB :=
    cont_respects_hsame sameTrap (hsame_refl sealRow) trapSealRealA trapSealRealB
  exact
    ⟨windowUnaryA, windowUnaryB, modulusUnaryA, modulusUnaryB, trapUnaryA, trapUnaryB,
      realUnaryA, realUnaryB, sameWindow, sameModulus, sameTrap, sameReal, realPkgA,
      realPkgB⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
