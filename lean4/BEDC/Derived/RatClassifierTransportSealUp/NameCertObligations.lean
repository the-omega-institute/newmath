import BEDC.Derived.RatClassifierTransportSealUp.WindowExhaustion
import BEDC.FKernel.Package.Core

namespace BEDC.Derived.RatClassifierTransportSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Meta.TasteGate

theorem RatClassifierTransportSealCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {Q S W D A H C N realRead provenance : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    FieldFaithful.fields (RatClassifierTransportSealUp.mk Q S W D A H C N) =
      [Q, S, W, D, A, H, C, N] →
      UnaryHistory Q →
        UnaryHistory S →
          UnaryHistory D →
            UnaryHistory H →
              Cont Q S W →
                Cont W D A →
                  Cont A H realRead →
                    PkgSig bundle provenance pkg →
                      UnaryHistory W ∧ UnaryHistory A ∧ UnaryHistory realRead ∧
                        Cont Q S W ∧ Cont W D A ∧ Cont A H realRead ∧
                          PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont FieldFaithful
  intro fields unaryQ unaryS unaryD unaryH routeQS routeWD routeAH provenancePkg
  have windowRows :=
    RatClassifierTransportSealCarrier_window_exhaustion fields unaryQ unaryS unaryD unaryH
      routeQS routeWD routeAH
  exact
    ⟨windowRows.left, windowRows.right.left, windowRows.right.right.left,
      windowRows.right.right.right.left, windowRows.right.right.right.right.left,
      windowRows.right.right.right.right.right, provenancePkg⟩

end BEDC.Derived.RatClassifierTransportSealUp
