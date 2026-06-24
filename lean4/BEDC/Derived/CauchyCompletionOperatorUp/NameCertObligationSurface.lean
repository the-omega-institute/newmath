import BEDC.Derived.CauchyCompletionOperatorUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyCompletionOperatorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyCompletionOperatorCarrier [AskSetup] [PackageSetup]
    (M B U S R D Q E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory M ∧ UnaryHistory B ∧ UnaryHistory U ∧ UnaryHistory S ∧
    UnaryHistory R ∧ UnaryHistory D ∧ UnaryHistory Q ∧ UnaryHistory E ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem CauchyCompletionOperatorCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {M B U S R D Q E H C P N boundaryRead finiteRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionOperatorCarrier M B U S R D Q E H C P N bundle pkg ->
      Cont M U boundaryRead ->
        Cont B S finiteRead ->
          Cont Q E sealRead ->
            PkgSig bundle N pkg ->
              UnaryHistory M ∧ UnaryHistory B ∧ UnaryHistory U ∧ UnaryHistory S ∧
                UnaryHistory R ∧ UnaryHistory D ∧ UnaryHistory Q ∧ UnaryHistory E ∧
                  UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
                    UnaryHistory boundaryRead ∧ UnaryHistory finiteRead ∧
                      UnaryHistory sealRead ∧ Cont M U boundaryRead ∧
                        Cont B S finiteRead ∧ Cont Q E sealRead ∧
                          PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier boundaryRoute finiteRoute sealRoute namePkg
  obtain ⟨mUnary, bUnary, uUnary, sUnary, rUnary, dUnary, qUnary, eUnary, hUnary,
    cUnary, pUnary, nUnary, provenancePkg, _carrierNamePkg⟩ := carrier
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed mUnary uUnary boundaryRoute
  have finiteUnary : UnaryHistory finiteRead :=
    unary_cont_closed bUnary sUnary finiteRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed qUnary eUnary sealRoute
  exact
    ⟨mUnary, bUnary, uUnary, sUnary, rUnary, dUnary, qUnary, eUnary, hUnary, cUnary,
      pUnary, nUnary, boundaryUnary, finiteUnary, sealUnary, boundaryRoute, finiteRoute,
      sealRoute, provenancePkg, namePkg⟩

end BEDC.Derived.CauchyCompletionOperatorUp
