import BEDC.Derived.StreamNameUp.SynchronizedWindowUnion

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem StreamNameFiniteWindowLatticeMeet_exhaustion [AskSetup] [PackageSetup]
    {leftWindow rightWindow refinement selectedLeft selectedRight synchronized replay dyadic realSeal
      localLeft localRight : BHist}
    {membershipBundle : ProbeBundle BHist} {packageBundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory leftWindow →
      UnaryHistory rightWindow →
        UnaryHistory refinement →
          UnaryHistory dyadic →
            InBundle selectedLeft membershipBundle →
              InBundle selectedRight membershipBundle →
                hsame selectedLeft selectedRight →
                  Cont leftWindow rightWindow synchronized →
                    Cont refinement synchronized replay →
                      Cont replay dyadic realSeal →
                        PkgSig packageBundle localLeft pkg →
                          PkgSig packageBundle localRight pkg →
                            UnaryHistory synchronized ∧ UnaryHistory replay ∧
                              UnaryHistory realSeal ∧ InBundle selectedLeft membershipBundle ∧
                                InBundle selectedRight membershipBundle ∧
                                  hsame selectedLeft selectedRight ∧
                                    Cont leftWindow rightWindow synchronized ∧
                                      Cont refinement synchronized replay ∧
                                        Cont replay dyadic realSeal ∧
                                          PkgSig packageBundle localLeft pkg ∧
                                            PkgSig packageBundle localRight pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont InBundle
  intro leftUnary rightUnary refinementUnary dyadicUnary selectedLeftMember selectedRightMember
    selectedSame windowSync refinementReplay replayDyadic leftPkg rightPkg
  have synchronizedUnary : UnaryHistory synchronized :=
    unary_cont_closed leftUnary rightUnary windowSync
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed refinementUnary synchronizedUnary refinementReplay
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed replayUnary dyadicUnary replayDyadic
  exact
    ⟨synchronizedUnary,
      replayUnary,
      realSealUnary,
      selectedLeftMember,
      selectedRightMember,
      selectedSame,
      windowSync,
      refinementReplay,
      replayDyadic,
      leftPkg,
      rightPkg⟩

end BEDC.Derived.StreamNameUp
