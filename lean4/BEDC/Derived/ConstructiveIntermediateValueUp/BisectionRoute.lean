import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ConstructiveIntermediateValueUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ConstructiveIntermediateValueCarrier [AskSetup] [PackageSetup]
    (I F S B H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory I ∧ UnaryHistory F ∧ UnaryHistory S ∧ UnaryHistory B ∧
    UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
      PkgSig bundle P pkg

theorem ConstructiveIntermediateValueBisectionRoute [AskSetup] [PackageSetup]
    {I F S B H C P N mapRead signRead bisectRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ConstructiveIntermediateValueCarrier I F S B H C P N bundle pkg ->
      Cont I F mapRead ->
        Cont mapRead S signRead ->
          Cont signRead B bisectRead ->
            Cont P N namedRead ->
              PkgSig bundle N pkg ->
                UnaryHistory mapRead ∧ UnaryHistory signRead ∧ UnaryHistory bisectRead ∧
                  UnaryHistory namedRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier mapRoute signRoute bisectRoute nameRoute namePkg
  obtain ⟨iUnary, fUnary, sUnary, bUnary, _hUnary, _cUnary, pUnary, nUnary,
    provenancePkg⟩ := carrier
  have mapUnary : UnaryHistory mapRead :=
    unary_cont_closed iUnary fUnary mapRoute
  have signUnary : UnaryHistory signRead :=
    unary_cont_closed mapUnary sUnary signRoute
  have bisectUnary : UnaryHistory bisectRead :=
    unary_cont_closed signUnary bUnary bisectRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed pUnary nUnary nameRoute
  exact ⟨mapUnary, signUnary, bisectUnary, namedUnary, provenancePkg, namePkg⟩

theorem ConstructiveIntermediateValueCarrier_l10_scope [AskSetup] [PackageSetup]
    {I F S B H C P N mapRead signRead bisectRead namedRead realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ConstructiveIntermediateValueCarrier I F S B H C P N bundle pkg ->
      Cont I F mapRead ->
        Cont mapRead S signRead ->
          Cont signRead B bisectRead ->
            Cont P N namedRead ->
              Cont bisectRead N realSeal ->
                PkgSig bundle N pkg ->
                  UnaryHistory mapRead ∧ UnaryHistory signRead ∧ UnaryHistory bisectRead ∧
                    UnaryHistory namedRead ∧ UnaryHistory realSeal ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier mapRoute signRoute bisectRoute nameRoute sealRoute namePkg
  have route :=
    ConstructiveIntermediateValueBisectionRoute carrier mapRoute signRoute bisectRoute
      nameRoute namePkg
  obtain ⟨_iUnary, _fUnary, _sUnary, _bUnary, _hUnary, _cUnary, _pUnary, nUnary,
    _provenancePkg⟩ := carrier
  obtain ⟨mapUnary, signUnary, bisectUnary, namedUnary, provenancePkg, namePkg'⟩ := route
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed bisectUnary nUnary sealRoute
  exact
    ⟨mapUnary, signUnary, bisectUnary, namedUnary, realSealUnary, provenancePkg, namePkg'⟩

end BEDC.Derived.ConstructiveIntermediateValueUp
