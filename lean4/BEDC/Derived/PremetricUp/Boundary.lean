import BEDC.Derived.PremetricUp.TasteGate
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PremetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def PremetricCarrier [AskSetup] [PackageSetup]
    (X U D Z S M H C Q N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory X ∧ UnaryHistory U ∧ UnaryHistory D ∧ UnaryHistory Z ∧
    UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory Q ∧ UnaryHistory N ∧ PkgSig bundle Q pkg ∧ PkgSig bundle N pkg

theorem PremetricZeroDistanceClassifierBoundary [AskSetup] [PackageSetup]
    {X U D Z S M H C Q N zeroRead reflectionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PremetricCarrier X U D Z S M H C Q N bundle pkg →
      Cont D Z zeroRead →
        Cont zeroRead S reflectionRead →
          PkgSig bundle reflectionRead pkg →
            UnaryHistory D ∧ UnaryHistory Z ∧ UnaryHistory zeroRead ∧
              UnaryHistory reflectionRead ∧ Cont D Z zeroRead ∧
                Cont zeroRead S reflectionRead ∧ PkgSig bundle reflectionRead pkg := by
  -- BEDC touchpoint anchor: PremetricCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier zeroRoute reflectionRoute reflectionPkg
  obtain ⟨_xUnary, _uUnary, dUnary, zUnary, sUnary, _mUnary, _hUnary, _cUnary,
    _qUnary, _nUnary, _qPkg, _nPkg⟩ := carrier
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed dUnary zUnary zeroRoute
  have reflectionUnary : UnaryHistory reflectionRead :=
    unary_cont_closed zeroUnary sUnary reflectionRoute
  exact
    ⟨dUnary, zUnary, zeroUnary, reflectionUnary, zeroRoute, reflectionRoute, reflectionPkg⟩

theorem PremetricCompletionBoundary [AskSetup] [PackageSetup]
    {X U D Z S M H C Q N completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PremetricCarrier X U D Z S M H C Q N bundle pkg →
      Cont S M completionRead →
        PkgSig bundle completionRead pkg →
          UnaryHistory X ∧ UnaryHistory U ∧ UnaryHistory D ∧ UnaryHistory Z ∧
            UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory completionRead ∧
              Cont S M completionRead ∧ PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: PremetricCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier completionRoute completionPkg
  obtain ⟨xUnary, uUnary, dUnary, zUnary, sUnary, mUnary, _hUnary, _cUnary,
    _qUnary, _nUnary, _qPkg, _nPkg⟩ := carrier
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed sUnary mUnary completionRoute
  exact
    ⟨xUnary, uUnary, dUnary, zUnary, sUnary, mUnary, completionUnary, completionRoute,
      completionPkg⟩

end BEDC.Derived.PremetricUp
