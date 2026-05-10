import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.DerivedFunctorUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def DerivedFunctorCarrier
    (functor resolution homology degree resolved endpoint : BHist) : Prop :=
  UnaryHistory degree ∧ Cont functor resolution resolved ∧ Cont resolved homology endpoint

theorem DerivedFunctorCarrier_resolution_append_readback
    {functor resolution homology degree resolved endpoint : BHist} :
    DerivedFunctorCarrier functor resolution homology degree resolved endpoint ->
      hsame resolved (append functor resolution) ∧
        hsame endpoint (append (append functor resolution) homology) ∧
          Cont functor resolution resolved ∧ Cont resolved homology endpoint := by
  intro carrier
  have resolvedReadback : hsame resolved (append functor resolution) :=
    carrier.right.left
  have endpointReadback :
      hsame endpoint (append (append functor resolution) homology) :=
    hsame_trans carrier.right.right
      (congrArg (fun h => append h homology) resolvedReadback)
  exact And.intro resolvedReadback
    (And.intro endpointReadback (And.intro carrier.right.left carrier.right.right))

theorem DerivedFunctorCarrier_boundary_over_transported_resolution
    {functor resolution homology degree resolved endpoint resolution' resolved' endpoint' : BHist} :
    DerivedFunctorCarrier functor resolution homology degree resolved endpoint ->
      hsame resolution resolution' ->
        Cont functor resolution' resolved' ->
          Cont resolved' homology endpoint' ->
            DerivedFunctorCarrier functor resolution' homology degree resolved' endpoint' ∧
              hsame resolved resolved' ∧ hsame endpoint endpoint' := by
  intro carrier sameResolution resolvedRow endpointRow
  have sameResolved : hsame resolved resolved' :=
    cont_respects_hsame (hsame_refl functor) sameResolution carrier.right.left resolvedRow
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameResolved (hsame_refl homology) carrier.right.right endpointRow
  exact And.intro
    (And.intro carrier.left (And.intro resolvedRow endpointRow))
    (And.intro sameResolved sameEndpoint)

theorem DerivedFunctorCarrier_classifier_stability
    {functor functor' resolution resolution' homology homology' degree degree'
      resolved resolved' endpoint endpoint' : BHist} :
    DerivedFunctorCarrier functor resolution homology degree resolved endpoint ->
      UnaryHistory degree' ->
        hsame functor functor' ->
          hsame resolution resolution' ->
            hsame homology homology' ->
              hsame degree degree' ->
                hsame endpoint endpoint' ->
                  Cont functor' resolution' resolved' ->
                    Cont resolved' homology' endpoint' ->
                      DerivedFunctorCarrier functor' resolution' homology' degree'
                          resolved' endpoint' ∧
                        hsame resolved resolved' := by
  intro carrier degreeUnary sameFunctor sameResolution sameHomology _sameDegree _sameEndpoint
    resolvedRow endpointRow
  have sameResolved : hsame resolved resolved' :=
    cont_respects_hsame sameFunctor sameResolution carrier.right.left resolvedRow
  have _endpointByRows : hsame endpoint endpoint' :=
    cont_respects_hsame sameResolved sameHomology carrier.right.right endpointRow
  exact And.intro
    (And.intro degreeUnary (And.intro resolvedRow endpointRow))
    sameResolved

theorem DerivedFunctorCarrier_namecert_obligation_surface
    {functor resolution homology degree resolved endpoint : BHist} :
    DerivedFunctorCarrier functor resolution homology degree resolved endpoint ->
      SemanticNameCert
        (fun row : BHist => DerivedFunctorCarrier functor resolution homology degree resolved endpoint ∧
          hsame row endpoint)
        (fun row : BHist => DerivedFunctorCarrier functor resolution homology degree resolved endpoint ∧
          hsame row endpoint)
        (fun row : BHist => DerivedFunctorCarrier functor resolution homology degree resolved endpoint ∧
          hsame row endpoint)
        hsame ∧
        hsame resolved (append functor resolution) ∧
          hsame endpoint (append (append functor resolution) homology) ∧
            Cont functor resolution resolved ∧ Cont resolved homology endpoint := by
  intro carrier
  have cert :
      SemanticNameCert
        (fun row : BHist => DerivedFunctorCarrier functor resolution homology degree resolved endpoint ∧
          hsame row endpoint)
        (fun row : BHist => DerivedFunctorCarrier functor resolution homology degree resolved endpoint ∧
          hsame row endpoint)
        (fun row : BHist => DerivedFunctorCarrier functor resolution homology degree resolved endpoint ∧
          hsame row endpoint)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint (And.intro carrier (hsame_refl endpoint))
      equiv_refl := by
        intro row _rowCarrier
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro row row' sameRows rowCarrier
        exact And.intro rowCarrier.left (hsame_trans (hsame_symm sameRows) rowCarrier.right)
    }
    pattern_sound := by
      intro _row rowCarrier
      exact rowCarrier
    ledger_sound := by
      intro _row rowCarrier
      exact rowCarrier
  }
  exact And.intro cert (DerivedFunctorCarrier_resolution_append_readback carrier)

def DerivedFunctorExactTriangleBoundaryCarrier
    (functor resolutionA resolutionB resolutionC homology degree resolvedA resolvedB resolvedC
      endpointA endpointB endpointC boundary : BHist) : Prop :=
  DerivedFunctorCarrier functor resolutionA homology degree resolvedA endpointA ∧
    DerivedFunctorCarrier functor resolutionB homology degree resolvedB endpointB ∧
      DerivedFunctorCarrier functor resolutionC homology degree resolvedC endpointC ∧
        UnaryHistory boundary

theorem DerivedFunctorExactTriangleBoundaryCarrier_scope
    {functor resolutionA resolutionB resolutionC homology degree resolvedA resolvedB resolvedC
      endpointA endpointB endpointC boundary boundaryEndpoint : BHist} :
    DerivedFunctorExactTriangleBoundaryCarrier functor resolutionA resolutionB resolutionC
        homology degree resolvedA resolvedB resolvedC endpointA endpointB endpointC boundary ->
      Cont endpointC boundary boundaryEndpoint ->
        UnaryHistory degree ∧
          DerivedFunctorCarrier functor resolutionA homology degree resolvedA endpointA ∧
            DerivedFunctorCarrier functor resolutionB homology degree resolvedB endpointB ∧
              DerivedFunctorCarrier functor resolutionC homology degree resolvedC endpointC ∧
                hsame boundaryEndpoint (append endpointC boundary) := by
  intro carrier boundaryRow
  exact And.intro carrier.left.left
    (And.intro carrier.left
      (And.intro carrier.right.left
        (And.intro carrier.right.right.left boundaryRow)))

end BEDC.Derived.DerivedFunctorUp
