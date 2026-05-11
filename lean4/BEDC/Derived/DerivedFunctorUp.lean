import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.DerivedFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DerivedFunctorCarrier
    (functor resolution homology degree resolved endpoint : BHist) : Prop :=
  UnaryHistory degree ∧ Cont functor resolution resolved ∧ Cont resolved homology endpoint

def DerivedFunctorResolutionSpineCarrier
    (abelian homology object spine cycle boundary functor degree provenance endpoint : BHist) :
    Prop :=
  UnaryHistory degree ∧ Cont functor spine object ∧ Cont object homology endpoint ∧
    Cont cycle boundary homology ∧ hsame provenance (append (append abelian homology) endpoint)

theorem DerivedFunctorResolutionSpineCarrier_obligation
    {abelian homology object spine cycle boundary functor degree provenance endpoint : BHist} :
    UnaryHistory degree ->
      Cont functor spine object ->
        Cont object homology endpoint ->
          Cont cycle boundary homology ->
            hsame provenance (append (append abelian homology) endpoint) ->
              DerivedFunctorResolutionSpineCarrier abelian homology object spine cycle boundary
                  functor degree provenance endpoint ∧
                hsame endpoint (append (append functor spine) homology) ∧
                  UnaryHistory degree := by
  intro degreeUnary spineRow endpointRow boundaryRow provenanceRow
  have objectReadback : hsame object (append functor spine) := spineRow
  have endpointReadback : hsame endpoint (append (append functor spine) homology) :=
    hsame_trans endpointRow (congrArg (fun h => append h homology) objectReadback)
  exact And.intro
    (And.intro degreeUnary
      (And.intro spineRow
        (And.intro endpointRow (And.intro boundaryRow provenanceRow))))
    (And.intro endpointReadback degreeUnary)

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

theorem DerivedFunctorCarrier_cycle_boundary_classifier_obligation
    {functor resolution homology degree resolved endpoint boundary boundaryEndpoint : BHist} :
    DerivedFunctorCarrier functor resolution homology degree resolved endpoint ->
      Cont endpoint boundary boundaryEndpoint ->
        UnaryHistory degree ∧ hsame resolved (append functor resolution) ∧
          hsame endpoint (append (append functor resolution) homology) ∧
            hsame boundaryEndpoint (append endpoint boundary) ∧
              Cont functor resolution resolved ∧ Cont resolved homology endpoint := by
  intro carrier boundaryRow
  have readback :=
    DerivedFunctorCarrier_resolution_append_readback
      (functor := functor) (resolution := resolution) (homology := homology)
      (degree := degree) (resolved := resolved) (endpoint := endpoint) carrier
  exact And.intro carrier.left
    (And.intro readback.left
      (And.intro readback.right.left
        (And.intro boundaryRow
          (And.intro readback.right.right.left readback.right.right.right))))

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

theorem DerivedFunctorCarrier_resolution_source_scope
    {functor resolution homology degree resolved endpoint : BHist} :
    DerivedFunctorCarrier functor resolution homology degree resolved endpoint ->
      exists F R H i c : BHist,
        UnaryHistory i ∧ Cont F R c ∧ Cont c H endpoint ∧
          hsame endpoint (append c H) := by
  intro carrier
  exact Exists.intro functor
    (Exists.intro resolution
      (Exists.intro homology
        (Exists.intro degree
          (Exists.intro resolved
            (And.intro carrier.left
              (And.intro carrier.right.left
                (And.intro carrier.right.right carrier.right.right)))))))

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

theorem DerivedFunctorExactTriangleBoundaryCarrier_connecting_morphism_readback
    {functor resolutionA resolutionB resolutionC homology degree resolvedA resolvedB resolvedC
      endpointA endpointB endpointC boundary connecting splice : BHist} :
    DerivedFunctorExactTriangleBoundaryCarrier functor resolutionA resolutionB resolutionC
        homology degree resolvedA resolvedB resolvedC endpointA endpointB endpointC boundary ->
      Cont endpointC boundary connecting ->
        Cont connecting endpointA splice ->
          DerivedFunctorCarrier functor resolutionA homology degree resolvedA endpointA ∧
            DerivedFunctorCarrier functor resolutionC homology degree resolvedC endpointC ∧
              hsame connecting (append endpointC boundary) ∧
                hsame splice (append (append endpointC boundary) endpointA) := by
  intro carrier connectingRow spliceRow
  have spliceReadback : hsame splice (append (append endpointC boundary) endpointA) :=
    hsame_trans spliceRow (congrArg (fun h => append h endpointA) connectingRow)
  exact And.intro carrier.left
    (And.intro carrier.right.right.left
      (And.intro connectingRow spliceReadback))

theorem DerivedFunctorExactTriangleBoundaryCarrier_long_exact_ledger_surface
    {functor resolutionA resolutionB resolutionC homology degree resolvedA resolvedB resolvedC
      endpointA endpointB endpointC boundary connecting splice : BHist} :
    DerivedFunctorExactTriangleBoundaryCarrier functor resolutionA resolutionB resolutionC
        homology degree resolvedA resolvedB resolvedC endpointA endpointB endpointC boundary ->
      Cont endpointC boundary connecting ->
        Cont connecting endpointA splice ->
          DerivedFunctorCarrier functor resolutionA homology degree resolvedA endpointA ∧
            DerivedFunctorCarrier functor resolutionB homology degree resolvedB endpointB ∧
              DerivedFunctorCarrier functor resolutionC homology degree resolvedC endpointC ∧
                hsame connecting (append endpointC boundary) ∧
                  hsame splice (append (append endpointC boundary) endpointA) ∧
                    UnaryHistory degree ∧ UnaryHistory boundary := by
  intro carrier connectingRow spliceRow
  have spliceReadback : hsame splice (append (append endpointC boundary) endpointA) :=
    hsame_trans spliceRow (congrArg (fun h => append h endpointA) connectingRow)
  exact And.intro carrier.left
    (And.intro carrier.right.left
      (And.intro carrier.right.right.left
        (And.intro connectingRow
          (And.intro spliceReadback
            (And.intro carrier.left.left carrier.right.right.right)))))

def DerivedFunctorDeltaSpliceSurface [AskSetup] [PackageSetup]
    (functor resolutionA resolutionB resolutionC homology degree resolvedA resolvedB resolvedC
      endpointA endpointB endpointC boundary connecting splice : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  DerivedFunctorExactTriangleBoundaryCarrier functor resolutionA resolutionB resolutionC homology
      degree resolvedA resolvedB resolvedC endpointA endpointB endpointC boundary ∧
    Cont endpointC boundary connecting ∧ Cont connecting endpointA splice ∧
      PkgSig bundle splice pkg

theorem DerivedFunctorDeltaSpliceSurface_short_exact_source_scope [AskSetup] [PackageSetup]
    {functor resolutionA resolutionB resolutionC homology degree resolvedA resolvedB resolvedC
      endpointA endpointB endpointC boundary connecting splice : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DerivedFunctorDeltaSpliceSurface functor resolutionA resolutionB resolutionC homology degree
        resolvedA resolvedB resolvedC endpointA endpointB endpointC boundary connecting splice
        bundle pkg ->
      DerivedFunctorCarrier functor resolutionA homology degree resolvedA endpointA ∧
        DerivedFunctorCarrier functor resolutionB homology degree resolvedB endpointB ∧
          DerivedFunctorCarrier functor resolutionC homology degree resolvedC endpointC ∧
            hsame connecting (append endpointC boundary) ∧
              hsame splice (append (append endpointC boundary) endpointA) ∧
                PkgSig bundle splice pkg := by
  intro surface
  have boundaryCarrier :
      DerivedFunctorExactTriangleBoundaryCarrier functor resolutionA resolutionB resolutionC
        homology degree resolvedA resolvedB resolvedC endpointA endpointB endpointC boundary :=
    surface.left
  have connectingRow : Cont endpointC boundary connecting :=
    surface.right.left
  have spliceRow : Cont connecting endpointA splice :=
    surface.right.right.left
  have spliceReadback : hsame splice (append (append endpointC boundary) endpointA) :=
    hsame_trans spliceRow (congrArg (fun row => append row endpointA) connectingRow)
  exact And.intro boundaryCarrier.left
    (And.intro boundaryCarrier.right.left
      (And.intro boundaryCarrier.right.right.left
        (And.intro connectingRow
          (And.intro spliceReadback surface.right.right.right))))

theorem DerivedFunctorDeltaSpliceSurface_connecting_row_ledger [AskSetup] [PackageSetup]
    {functor resolutionA resolutionB resolutionC homology degree resolvedA resolvedB resolvedC endpointA
      endpointB endpointC endpointC' boundary boundary' connecting connecting' splice splice' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DerivedFunctorDeltaSpliceSurface functor resolutionA resolutionB resolutionC homology degree
        resolvedA resolvedB resolvedC endpointA endpointB endpointC boundary connecting splice
        bundle pkg ->
      hsame endpointC endpointC' ->
        Cont resolvedC homology endpointC' ->
          hsame boundary boundary' ->
            Cont endpointC' boundary' connecting' ->
              Cont connecting' endpointA splice' ->
                PkgSig bundle splice' pkg ->
                  DerivedFunctorDeltaSpliceSurface functor resolutionA resolutionB resolutionC
                      homology degree resolvedA resolvedB resolvedC endpointA endpointB endpointC'
                      boundary' connecting' splice' bundle pkg ∧
                    hsame connecting connecting' ∧ hsame splice splice' := by
  intro surface sameEndpointC endpointCRow sameBoundary connectingRow spliceRow splicePkg
  have boundaryCarrier :
      DerivedFunctorExactTriangleBoundaryCarrier functor resolutionA resolutionB resolutionC
        homology degree resolvedA resolvedB resolvedC endpointA endpointB endpointC boundary :=
    surface.left
  have thirdCarrier' :
      DerivedFunctorCarrier functor resolutionC homology degree resolvedC endpointC' :=
    ⟨boundaryCarrier.right.right.left.left,
      boundaryCarrier.right.right.left.right.left,
      endpointCRow⟩
  have boundaryCarrier' :
      DerivedFunctorExactTriangleBoundaryCarrier functor resolutionA resolutionB resolutionC
        homology degree resolvedA resolvedB resolvedC endpointA endpointB endpointC' boundary' :=
    ⟨boundaryCarrier.left,
      boundaryCarrier.right.left,
      thirdCarrier',
      unary_transport boundaryCarrier.right.right.right sameBoundary⟩
  have sameConnecting : hsame connecting connecting' :=
    cont_respects_hsame sameEndpointC sameBoundary surface.right.left connectingRow
  have sameSplice : hsame splice splice' :=
    cont_respects_hsame sameConnecting (hsame_refl endpointA) surface.right.right.left spliceRow
  have transportedSurface :
      DerivedFunctorDeltaSpliceSurface functor resolutionA resolutionB resolutionC homology degree
        resolvedA resolvedB resolvedC endpointA endpointB endpointC' boundary' connecting' splice'
        bundle pkg :=
    ⟨boundaryCarrier', connectingRow, spliceRow, splicePkg⟩
  exact ⟨transportedSurface, sameConnecting, sameSplice⟩

end BEDC.Derived.DerivedFunctorUp
