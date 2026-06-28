import BEDC.Derived.SturmRootIsolationUp.SignVariationHandoff
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SturmRootIsolationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SturmRootIsolationCarrier [AskSetup] [PackageSetup]
    (P I D V B W R S H C Q N branchRead replayRead sealRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory P ∧ UnaryHistory I ∧ UnaryHistory D ∧ UnaryHistory V ∧
    UnaryHistory B ∧ UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory S ∧
      UnaryHistory H ∧ UnaryHistory C ∧ Cont B H branchRead ∧
        Cont branchRead C replayRead ∧ Cont replayRead S sealRead ∧
          PkgSig bundle Q pkg ∧ PkgSig bundle N pkg

theorem SturmRootIsolationCarrier_row_unary_envelope [AskSetup] [PackageSetup]
    {P I D V B W R S H C Q N branchRead replayRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SturmRootIsolationCarrier P I D V B W R S H C Q N branchRead replayRead sealRead
        bundle pkg →
      UnaryHistory branchRead ∧ UnaryHistory replayRead ∧ UnaryHistory sealRead ∧
        Cont B H branchRead ∧ Cont branchRead C replayRead ∧ Cont replayRead S sealRead ∧
          PkgSig bundle Q pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier
  unfold SturmRootIsolationCarrier at carrier
  obtain ⟨_unaryP, _unaryI, _unaryD, _unaryV, unaryB, _unaryW, _unaryR, unaryS,
    unaryH, unaryC, branchRoute, replayRoute, sealRoute, qPkg, nPkg⟩ := carrier
  have branchUnary : UnaryHistory branchRead :=
    unary_cont_closed unaryB unaryH branchRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed branchUnary unaryC replayRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed replayUnary unaryS sealRoute
  exact
    ⟨branchUnary, replayUnary, sealUnary, branchRoute, replayRoute, sealRoute, qPkg, nPkg⟩

end BEDC.Derived.SturmRootIsolationUp
