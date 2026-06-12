import BEDC.Derived.DyadicIntervalArithmeticUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicIntervalArithmeticUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicIntervalArithmeticCarrier [AskSetup] [PackageSetup]
    (lower upper order addDelta mulDelta refinement enclosure _transport replay provenance
      localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory lower ∧
    UnaryHistory upper ∧
      UnaryHistory addDelta ∧
        UnaryHistory mulDelta ∧
          UnaryHistory refinement ∧
            UnaryHistory replay ∧
              Cont lower upper order ∧
                Cont order addDelta enclosure ∧
                  Cont enclosure replay refinement ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle localCert pkg

theorem DyadicIntervalArithmeticCarrier_enclosure_soundness [AskSetup] [PackageSetup]
    {lower upper order addDelta mulDelta refinement enclosure transport replay provenance
      localCert operationRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalArithmeticCarrier lower upper order addDelta mulDelta refinement enclosure
      transport replay provenance localCert bundle pkg →
      Cont order addDelta operationRead →
        Cont operationRead enclosure handoffRead →
          PkgSig bundle handoffRead pkg →
            UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory order ∧
              UnaryHistory operationRead ∧ UnaryHistory handoffRead ∧
                Cont order addDelta operationRead ∧
                  Cont operationRead enclosure handoffRead ∧
                    PkgSig bundle handoffRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier operationCont handoffCont handoffPkg
  cases carrier with
  | intro lowerUnary carrier =>
      cases carrier with
      | intro upperUnary carrier =>
          cases carrier with
          | intro addDeltaUnary carrier =>
              cases carrier with
              | intro _mulDeltaUnary carrier =>
                  cases carrier with
                  | intro _refinementUnary carrier =>
                      cases carrier with
                      | intro _replayUnary carrier =>
                          cases carrier with
                          | intro orderCont carrier =>
                              cases carrier with
                              | intro enclosureCont _carrier =>
                                  have orderUnary : UnaryHistory order :=
                                    unary_cont_closed lowerUnary upperUnary orderCont
                                  have operationUnary : UnaryHistory operationRead :=
                                    unary_cont_closed orderUnary addDeltaUnary operationCont
                                  have enclosureUnary : UnaryHistory enclosure :=
                                    unary_cont_closed orderUnary addDeltaUnary enclosureCont
                                  have handoffUnary : UnaryHistory handoffRead :=
                                    unary_cont_closed operationUnary enclosureUnary handoffCont
                                  exact
                                    ⟨lowerUnary, upperUnary, orderUnary, operationUnary,
                                      handoffUnary, operationCont, handoffCont, handoffPkg⟩

theorem DyadicIntervalArithmeticCarrier_refinement_monotonicity [AskSetup] [PackageSetup]
    {lower upper order addDelta mulDelta refinement enclosure transport replay provenance
      localCert operationRead handoffRead refinedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalArithmeticCarrier lower upper order addDelta mulDelta refinement enclosure
      transport replay provenance localCert bundle pkg →
      Cont order addDelta operationRead →
        Cont operationRead enclosure handoffRead →
          Cont handoffRead refinement refinedRead →
            PkgSig bundle refinedRead pkg →
              UnaryHistory operationRead ∧ UnaryHistory handoffRead ∧
                UnaryHistory refinedRead ∧ Cont order addDelta operationRead ∧
                  Cont operationRead enclosure handoffRead ∧
                    Cont handoffRead refinement refinedRead ∧ PkgSig bundle refinedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier operationCont handoffCont refinedCont refinedPkg
  obtain
    ⟨lowerUnary, upperUnary, addDeltaUnary, _mulDeltaUnary, refinementUnary, _replayUnary,
      orderCont, enclosureCont, _refinementCont, _provenancePkg, _localCertPkg⟩ := carrier
  have orderUnary : UnaryHistory order :=
    unary_cont_closed lowerUnary upperUnary orderCont
  have operationUnary : UnaryHistory operationRead :=
    unary_cont_closed orderUnary addDeltaUnary operationCont
  have enclosureUnary : UnaryHistory enclosure :=
    unary_cont_closed orderUnary addDeltaUnary enclosureCont
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed operationUnary enclosureUnary handoffCont
  have refinedUnary : UnaryHistory refinedRead :=
    unary_cont_closed handoffUnary refinementUnary refinedCont
  exact
    ⟨operationUnary, handoffUnary, refinedUnary, operationCont, handoffCont, refinedCont,
      refinedPkg⟩

theorem DyadicIntervalArithmeticCarrier_endpoint_order_transport [AskSetup] [PackageSetup]
    {lower upper order addDelta mulDelta refinement enclosure transport replay provenance
      localCert transportedOrder : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalArithmeticCarrier lower upper order addDelta mulDelta refinement enclosure
      transport replay provenance localCert bundle pkg →
      Cont order replay transportedOrder →
        PkgSig bundle transportedOrder pkg →
          UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory order ∧
            UnaryHistory replay ∧ UnaryHistory transportedOrder ∧
              Cont lower upper order ∧ Cont order replay transportedOrder ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle transportedOrder pkg := by
  -- BEDC touchpoint anchor: DyadicIntervalArithmeticCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier orderReplayTransport transportedPkg
  obtain
    ⟨lowerUnary, upperUnary, _addDeltaUnary, _mulDeltaUnary, _refinementUnary, replayUnary,
      orderCont, _enclosureCont, _refinementCont, provenancePkg, _localCertPkg⟩ := carrier
  have orderUnary : UnaryHistory order :=
    unary_cont_closed lowerUnary upperUnary orderCont
  have transportedUnary : UnaryHistory transportedOrder :=
    unary_cont_closed orderUnary replayUnary orderReplayTransport
  exact
    ⟨lowerUnary, upperUnary, orderUnary, replayUnary, transportedUnary, orderCont,
      orderReplayTransport, provenancePkg, transportedPkg⟩

end BEDC.Derived.DyadicIntervalArithmeticUp
