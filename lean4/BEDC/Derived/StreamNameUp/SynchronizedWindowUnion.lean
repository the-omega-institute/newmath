import BEDC.Derived.StreamNameUp
import BEDC.FKernel.Package

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem StreamnameSynchronizedWindowUnionCarrier [AskSetup] [PackageSetup]
    {leftWindow rightWindow refinement selectedLeft selectedRight synchronized replay name : BHist}
    {membershipBundle : ProbeBundle BHist} {packageBundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory leftWindow ->
      UnaryHistory rightWindow ->
        UnaryHistory refinement ->
          InBundle selectedLeft membershipBundle ->
            InBundle selectedRight membershipBundle ->
              hsame selectedLeft selectedRight ->
                Cont leftWindow rightWindow synchronized ->
                  Cont refinement synchronized replay ->
                    PkgSig packageBundle name pkg ->
                      UnaryHistory synchronized ∧ InBundle selectedLeft membershipBundle ∧
                        InBundle selectedRight membershipBundle ∧ hsame selectedLeft selectedRight ∧
                          Cont leftWindow rightWindow synchronized ∧
                            Cont refinement synchronized replay ∧ PkgSig packageBundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro leftUnary rightUnary _refinementUnary selectedLeftMember selectedRightMember selectedSame
    windowSync refinementReplay namePkg
  have synchronizedUnary : UnaryHistory synchronized :=
    unary_cont_closed leftUnary rightUnary windowSync
  exact
    ⟨synchronizedUnary, selectedLeftMember, selectedRightMember, selectedSame, windowSync,
      refinementReplay, namePkg⟩

end BEDC.Derived.StreamNameUp
