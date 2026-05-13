import BEDC.Derived.ObserverLocalityCellUp.TasteGate
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ObserverLocalityCellUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ObserverLocalityCellPacket [AskSetup] [PackageSetup]
    (observerLeft observerRight eventLeft eventRight gapLeft gapRight transport continuation
      provenance nameCert : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  UnaryHistory observerLeft ∧
    UnaryHistory observerRight ∧
      UnaryHistory eventLeft ∧
        UnaryHistory eventRight ∧
          UnaryHistory gapLeft ∧
            UnaryHistory gapRight ∧
              UnaryHistory transport ∧
                UnaryHistory continuation ∧
                  UnaryHistory provenance ∧
                    UnaryHistory nameCert ∧
                      Cont observerLeft eventLeft gapLeft ∧
                        Cont observerRight eventRight gapRight ∧
                          Cont gapLeft gapRight transport ∧
                            Cont transport continuation provenance ∧
                              PkgSig bundle nameCert pkg

theorem ObserverLocalityCellPacket_paired_gap_transport [AskSetup] [PackageSetup]
    {observerLeft observerRight eventLeft eventRight gapLeft gapRight transport continuation
      provenance nameCert observerLeft' observerRight' eventLeft' eventRight' gapLeft'
      gapRight' transport' : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverLocalityCellPacket observerLeft observerRight eventLeft eventRight gapLeft gapRight
      transport continuation provenance nameCert bundle pkg →
    hsame observerLeft observerLeft' →
    hsame eventLeft eventLeft' →
    hsame observerRight observerRight' →
    hsame eventRight eventRight' →
    Cont observerLeft' eventLeft' gapLeft' →
    Cont observerRight' eventRight' gapRight' →
    Cont gapLeft' gapRight' transport' →
    hsame gapLeft gapLeft' ∧
      hsame gapRight gapRight' ∧
        hsame transport transport' ∧
          UnaryHistory gapLeft' ∧ UnaryHistory gapRight' ∧ UnaryHistory transport' := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory Pkg
  intro packet sameObserverLeft sameEventLeft sameObserverRight sameEventRight
    gapLeftRow gapRightRow transportRow
  have gapLeftUnary : UnaryHistory gapLeft :=
    packet.right.right.right.right.left
  have gapRightUnary : UnaryHistory gapRight :=
    packet.right.right.right.right.right.left
  have transportUnary : UnaryHistory transport :=
    packet.right.right.right.right.right.right.left
  have originalGapLeftRow : Cont observerLeft eventLeft gapLeft :=
    packet.right.right.right.right.right.right.right.right.right.right.left
  have originalGapRightRow : Cont observerRight eventRight gapRight :=
    packet.right.right.right.right.right.right.right.right.right.right.right.left
  have originalTransportRow : Cont gapLeft gapRight transport :=
    packet.right.right.right.right.right.right.right.right.right.right.right.right.left
  have sameGapLeft : hsame gapLeft gapLeft' :=
    cont_respects_hsame sameObserverLeft sameEventLeft originalGapLeftRow gapLeftRow
  have sameGapRight : hsame gapRight gapRight' :=
    cont_respects_hsame sameObserverRight sameEventRight originalGapRightRow gapRightRow
  have sameTransport : hsame transport transport' :=
    cont_respects_hsame sameGapLeft sameGapRight originalTransportRow transportRow
  constructor
  · exact sameGapLeft
  · constructor
    · exact sameGapRight
    · constructor
      · exact sameTransport
      · constructor
        · exact unary_transport gapLeftUnary sameGapLeft
        · constructor
          · exact unary_transport gapRightUnary sameGapRight
          · exact unary_transport transportUnary sameTransport

end BEDC.Derived.ObserverLocalityCellUp
