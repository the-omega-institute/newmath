import BEDC.Derived.IshiharaTrickUp.TasteGate
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.IshiharaTrickUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def IshiharaTrickCarrier [AskSetup] [PackageSetup]
    (S R T W D E A H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory T ∧ UnaryHistory W ∧ UnaryHistory D ∧
    UnaryHistory E ∧ UnaryHistory A ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ Cont T W A ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem IshiharaTrickCarrier_branch_stability [AskSetup] [PackageSetup]
    {S R T W D E A H C P N S' R' T' W' D' E' A' H' C' P' N' branch branch' :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IshiharaTrickCarrier S R T W D E A H C P N bundle pkg ->
      IshiharaTrickCarrier S' R' T' W' D' E' A' H' C' P' N' bundle pkg ->
        hsame T T' ->
          hsame W W' ->
            Cont T W branch ->
              Cont T' W' branch' ->
                PkgSig bundle branch' pkg ->
                  hsame branch branch' ∧ UnaryHistory branch ∧ UnaryHistory branch' ∧
                    Cont T W branch ∧ Cont T' W' branch' ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle branch' pkg := by
  -- BEDC touchpoint anchor: IshiharaTrickCarrier BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro sourceCarrier targetCarrier sameT sameW sourceBranch targetBranch branchPkg
  obtain ⟨_SUnary, _RUnary, TUnary, WUnary, _DUnary, _EUnary, _AUnary, _HUnary, _CUnary,
    _PUnary, _NUnary, _sourceBoundary, sourcePkg, _sourceNamePkg⟩ := sourceCarrier
  obtain ⟨_SUnary', _RUnary', TUnary', WUnary', _DUnary', _EUnary', _AUnary', _HUnary',
    _CUnary', _PUnary', _NUnary', _targetBoundary, _targetPkg, _targetNamePkg⟩ :=
    targetCarrier
  have sameBranch : hsame branch branch' :=
    cont_respects_hsame sameT sameW sourceBranch targetBranch
  have branchUnary : UnaryHistory branch :=
    unary_cont_closed TUnary WUnary sourceBranch
  have branchUnary' : UnaryHistory branch' :=
    unary_cont_closed TUnary' WUnary' targetBranch
  exact
    ⟨sameBranch, branchUnary, branchUnary', sourceBranch, targetBranch, sourcePkg, branchPkg⟩

end BEDC.Derived.IshiharaTrickUp
