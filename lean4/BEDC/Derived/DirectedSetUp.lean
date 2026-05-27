import BEDC.Derived.DirectedSetUp.TasteGate

namespace BEDC.Derived.DirectedSetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DirectedSetCarrier_fields_faithful :
    ∀ x y : DirectedSetUp, directedSetFields x = directedSetFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 Le1 W1 U1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 Le2 W2 U2 H2 C2 P2 N2 =>
          cases hfields
          rfl

theorem DirectedSetCarrier_preorder_stability_obligation [AskSetup] [PackageSetup]
    {I Le W U H C P N comparisonRead transportedRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DirectedSetPacket I Le W U H C P N bundle pkg →
      Cont I Le comparisonRead →
        Cont comparisonRead H transportedRead →
          Cont transportedRead C replayRead →
            PkgSig bundle replayRead pkg →
              UnaryHistory I ∧ UnaryHistory Le ∧ UnaryHistory comparisonRead ∧
                UnaryHistory transportedRead ∧ UnaryHistory replayRead ∧
                  Cont I Le comparisonRead ∧ Cont comparisonRead H transportedRead ∧
                    Cont transportedRead C replayRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle replayRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet comparisonRoute transportRoute replayRoute replayPkg
  obtain ⟨iUnary, leUnary, _wUnary, _uUnary, _windowUnary, hUnary, cUnary, _nUnary,
    _wuh, _hcn, pPkg⟩ := packet
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed iUnary leUnary comparisonRoute
  have transportedUnary : UnaryHistory transportedRead :=
    unary_cont_closed comparisonUnary hUnary transportRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportedUnary cUnary replayRoute
  exact
    ⟨iUnary, leUnary, comparisonUnary, transportedUnary, replayUnary, comparisonRoute,
      transportRoute, replayRoute, pPkg, replayPkg⟩

theorem DirectedSetCarrier_cofinal_merge_obligation [AskSetup] [PackageSetup]
    {I Le W U H C P N firstWindow firstWitness secondWindow secondWitness mergedWindow
      mergedWitness replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DirectedSetPacket I Le W U H C P N bundle pkg ->
      Cont W firstWindow firstWitness ->
        Cont W secondWindow secondWitness ->
          Cont firstWitness secondWitness mergedWindow ->
            Cont W mergedWindow mergedWitness ->
              Cont mergedWitness H replayRead ->
                PkgSig bundle replayRead pkg ->
                  UnaryHistory firstWindow /\ UnaryHistory secondWindow /\
                    UnaryHistory mergedWindow /\ UnaryHistory mergedWitness /\
                      UnaryHistory replayRead /\ Cont W firstWindow firstWitness /\
                        Cont W secondWindow secondWitness /\
                          Cont firstWitness secondWitness mergedWindow /\
                            Cont W mergedWindow mergedWitness /\
                              Cont mergedWitness H replayRead /\ PkgSig bundle P pkg /\
                                PkgSig bundle replayRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet firstRoute secondRoute mergeRoute witnessRoute replayRoute replayPkg
  obtain ⟨_iUnary, _leUnary, wUnary, _uUnary, windowUnary, hUnary, _cUnary, _nUnary,
    _wuh, _hcn, pPkg⟩ := packet
  have firstWindowUnary : UnaryHistory firstWindow :=
    windowUnary firstRoute
  have secondWindowUnary : UnaryHistory secondWindow :=
    windowUnary secondRoute
  have firstWitnessUnary : UnaryHistory firstWitness :=
    unary_cont_closed wUnary firstWindowUnary firstRoute
  have secondWitnessUnary : UnaryHistory secondWitness :=
    unary_cont_closed wUnary secondWindowUnary secondRoute
  have mergedWindowUnary : UnaryHistory mergedWindow :=
    unary_cont_closed firstWitnessUnary secondWitnessUnary mergeRoute
  have mergedWitnessUnary : UnaryHistory mergedWitness :=
    unary_cont_closed wUnary mergedWindowUnary witnessRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed mergedWitnessUnary hUnary replayRoute
  exact
    ⟨firstWindowUnary, secondWindowUnary, mergedWindowUnary, mergedWitnessUnary,
      replayUnary, firstRoute, secondRoute, mergeRoute, witnessRoute, replayRoute, pPkg,
      replayPkg⟩

end BEDC.Derived.DirectedSetUp
