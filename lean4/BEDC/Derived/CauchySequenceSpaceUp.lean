import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchySequenceSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchySequenceSpaceCarrierSurface [AskSetup] [PackageSetup]
    (F sigma W epsilon Q H C P N endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory F ∧ UnaryHistory sigma ∧ UnaryHistory W ∧ UnaryHistory epsilon ∧
    UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ UnaryHistory endpoint ∧ Cont F sigma W ∧
        Cont W epsilon Q ∧ Cont Q N endpoint ∧ PkgSig bundle endpoint pkg

theorem CauchySequenceSpaceCommonWindowClassifierTransport [AskSetup] [PackageSetup]
    {F sigma W epsilon Q H C P N endpoint F' sigma' W' epsilon' Q' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceSpaceCarrierSurface F sigma W epsilon Q H C P N endpoint bundle pkg ->
      hsame F F' ->
        hsame sigma sigma' ->
          hsame W W' ->
            hsame epsilon epsilon' ->
              Cont F' sigma' W' ->
                Cont W' epsilon' Q' ->
                  Cont Q' N endpoint' ->
                    PkgSig bundle endpoint' pkg ->
                      CauchySequenceSpaceCarrierSurface F' sigma' W' epsilon' Q' H C P N
                          endpoint' bundle pkg ∧
                        hsame Q Q' ∧ hsame endpoint endpoint' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier sameF sameSigma sameW sameEpsilon windowRoute toleranceRoute endpointRoute
    pkgSig'
  obtain ⟨fUnary, sigmaUnary, wUnary, epsilonUnary, _qUnary, hUnary, cUnary, pUnary,
    nUnary, _endpointUnary, _oldWindowRoute, oldToleranceRoute, oldEndpointRoute,
    _pkgSig⟩ := carrier
  have fUnary' : UnaryHistory F' := unary_transport fUnary sameF
  have sigmaUnary' : UnaryHistory sigma' := unary_transport sigmaUnary sameSigma
  have wUnary' : UnaryHistory W' := unary_transport wUnary sameW
  have epsilonUnary' : UnaryHistory epsilon' := unary_transport epsilonUnary sameEpsilon
  have qSame : hsame Q Q' :=
    cont_respects_hsame sameW sameEpsilon oldToleranceRoute toleranceRoute
  have qUnary' : UnaryHistory Q' :=
    unary_cont_closed wUnary' epsilonUnary' toleranceRoute
  have endpointSame : hsame endpoint endpoint' :=
    cont_respects_hsame qSame (hsame_refl N) oldEndpointRoute endpointRoute
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed qUnary' nUnary endpointRoute
  exact
    ⟨⟨fUnary', sigmaUnary', wUnary', epsilonUnary', qUnary', hUnary, cUnary, pUnary,
      nUnary, endpointUnary', windowRoute, toleranceRoute, endpointRoute, pkgSig'⟩,
      qSame, endpointSame⟩

def CauchySequenceSpaceCarrier [AskSetup] [PackageSetup]
    (family schedule window tolerance completion transport route name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory family ∧ UnaryHistory schedule ∧ UnaryHistory window ∧
    UnaryHistory tolerance ∧ UnaryHistory completion ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory name ∧ Cont family schedule window ∧
        Cont window tolerance completion ∧ Cont completion transport route ∧
          PkgSig bundle route pkg ∧ PkgSig bundle name pkg

theorem CauchySequenceSpaceCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    {family schedule window tolerance completion transport route name : BHist} :
    CauchySequenceSpaceCarrier family schedule window tolerance completion transport route name
        bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          CauchySequenceSpaceCarrier family schedule window tolerance completion transport route
            name bundle pkg ∧ hsame row completion)
        (fun row : BHist =>
          CauchySequenceSpaceCarrier family schedule window tolerance completion transport route
            name bundle pkg ∧ hsame row completion)
        (fun row : BHist =>
          CauchySequenceSpaceCarrier family schedule window tolerance completion transport route
            name bundle pkg ∧ hsame row completion)
        hsame := by
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro completion (And.intro carrier (hsame_refl completion))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.CauchySequenceSpaceUp
