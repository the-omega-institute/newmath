import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.QuasiBanachUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def QuasiBanachCarrier [AskSetup] [PackageSetup]
    (X A Z M T F E C H R P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig NameCert
  UnaryHistory X ∧ UnaryHistory A ∧ UnaryHistory Z ∧ UnaryHistory M ∧ UnaryHistory T ∧
    UnaryHistory F ∧ UnaryHistory E ∧ UnaryHistory C ∧ UnaryHistory H ∧ UnaryHistory R ∧
      UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem QuasiBanachCarrier_metric_completion_handoff [AskSetup] [PackageSetup]
    {X A Z M T F E C H R P N triangleRead filterRead embeddingRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuasiBanachCarrier X A Z M T F E C H R P N bundle pkg →
      Cont M T triangleRead →
        Cont triangleRead F filterRead →
          Cont filterRead E embeddingRead →
            Cont embeddingRead C completionRead →
              PkgSig bundle completionRead pkg →
                UnaryHistory M ∧ UnaryHistory T ∧ UnaryHistory F ∧ UnaryHistory E ∧
                  UnaryHistory C ∧ UnaryHistory triangleRead ∧ UnaryHistory filterRead ∧
                    UnaryHistory embeddingRead ∧ UnaryHistory completionRead ∧
                      Cont M T triangleRead ∧ Cont triangleRead F filterRead ∧
                        Cont filterRead E embeddingRead ∧
                          Cont embeddingRead C completionRead ∧ PkgSig bundle P pkg ∧
                            PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier triangleRoute filterRoute embeddingRoute completionRoute completionPkg
  obtain ⟨_xUnary, _aUnary, _zUnary, mUnary, tUnary, fUnary, eUnary, cUnary, _hUnary,
    _rUnary, _pUnary, _nUnary, pPkg, _nPkg⟩ := carrier
  have triangleUnary : UnaryHistory triangleRead :=
    unary_cont_closed mUnary tUnary triangleRoute
  have filterUnary : UnaryHistory filterRead :=
    unary_cont_closed triangleUnary fUnary filterRoute
  have embeddingUnary : UnaryHistory embeddingRead :=
    unary_cont_closed filterUnary eUnary embeddingRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed embeddingUnary cUnary completionRoute
  exact
    ⟨mUnary, tUnary, fUnary, eUnary, cUnary, triangleUnary, filterUnary, embeddingUnary,
      completionUnary, triangleRoute, filterRoute, embeddingRoute, completionRoute, pPkg,
      completionPkg⟩

end BEDC.Derived.QuasiBanachUp
