import BEDC.Derived.AffineVarUp
import BEDC.Derived.PolynomialUp
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Units
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ProjectiveVarUp

open BEDC.Derived.AffineVarUp
open BEDC.Derived.PolynomialUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ProjectiveVarCarrier_obligation_rows
    {point polynomial eval package endpoint : BHist} {family : ProbeBundle BHist} :
    AffineFiniteFamilyZeroLocus (fun h : BHist => hsame h BHist.Empty)
        (fun p x : BHist =>
          PolynomialSingletonClassifier p BHist.Empty ∧ hsame x BHist.Empty)
        family point ->
      PolynomialSingletonClassifier polynomial BHist.Empty ->
        InBundle polynomial family ->
          Cont point polynomial eval ->
            hsame package eval ->
              UnaryHistory point ∧ PolynomialSingletonCarrier polynomial ∧
                PolynomialSingletonClassifier eval BHist.Empty ∧ hsame package BHist.Empty := by
  intro locus polynomialClassified memberPolynomial evalRow packageEval
  have pointEmpty : hsame point BHist.Empty := locus.left
  have pointUnary : UnaryHistory point :=
    unary_transport unary_empty (hsame_symm pointEmpty)
  have equationRow :
      PolynomialSingletonClassifier polynomial BHist.Empty ∧ hsame point BHist.Empty :=
    locus.right memberPolynomial
  have evalClassified : PolynomialSingletonClassifier eval BHist.Empty :=
    PolynomialSingletonClassifier_cont_result_empty_classified pointEmpty
      equationRow.left.left evalRow
  have packageEmpty : hsame package BHist.Empty :=
    hsame_trans packageEval evalClassified.left
  exact And.intro pointUnary
    (And.intro polynomialClassified.left (And.intro evalClassified packageEmpty))

theorem ProjectiveVarVisibleCarrier_endpoint_exactness
    {family : ProbeBundle BHist} {chart homogeneous projectiveSpace zeroEval endpoint : BHist} :
    AffineFiniteFamilyZeroLocus (fun h : BHist => hsame h BHist.Empty)
        (fun poly point : BHist => PolynomialSingletonClassifier poly point) family chart ->
      PolynomialSingletonClassifier homogeneous BHist.Empty ->
        hsame projectiveSpace chart ->
          Cont projectiveSpace zeroEval endpoint ->
            hsame zeroEval BHist.Empty ->
              hsame endpoint chart ∧
                AffineFiniteFamilyZeroLocus (fun h : BHist => hsame h BHist.Empty)
                  (fun poly point : BHist => PolynomialSingletonClassifier poly point)
                  family endpoint := by
  intro chartLocus _homogeneousZero sameProjectiveSpace endpointRow zeroEvalEmpty
  have endpointProjective : hsame endpoint projectiveSpace :=
    cont_right_unit_result (by
      cases zeroEvalEmpty
      exact endpointRow)
  have endpointChart : hsame endpoint chart :=
    hsame_trans endpointProjective sameProjectiveSpace
  have endpointEmpty : hsame endpoint BHist.Empty :=
    hsame_trans endpointChart chartLocus.left
  have endpointLocus :
      AffineFiniteFamilyZeroLocus (fun h : BHist => hsame h BHist.Empty)
        (fun poly point : BHist => PolynomialSingletonClassifier poly point) family endpoint :=
    And.intro endpointEmpty
      (by
        intro p member
        have chartClassified : PolynomialSingletonClassifier p chart :=
          chartLocus.right member
        have endpointClassified : PolynomialSingletonClassifier p endpoint :=
          And.intro chartClassified.left
            (And.intro endpointEmpty
              (hsame_trans chartClassified.right.right (hsame_symm endpointChart)))
        exact endpointClassified)
  exact And.intro endpointChart endpointLocus

theorem ProjectiveVarHomogeneousZeroLocus_visible_package
    {F : ProbeBundle BHist} {x scale projectiveEndpoint : BHist} :
    AffineFiniteFamilyZeroLocus PolynomialSingletonCarrier PolynomialSingletonClassifier F x ->
      PolynomialSingletonCarrier scale ->
        Cont x scale projectiveEndpoint ->
          PolynomialSingletonCarrier projectiveEndpoint ∧
            AffineFiniteFamilyZeroLocus PolynomialSingletonCarrier PolynomialSingletonClassifier F
              projectiveEndpoint := by
  intro locus scaleCarrier projectiveRow
  have xCarrier : PolynomialSingletonCarrier x := locus.left
  have endpointCarrier : PolynomialSingletonCarrier projectiveEndpoint :=
    cont_respects_hsame xCarrier scaleCarrier projectiveRow (cont_right_unit BHist.Empty)
  have xEndpointClassified : PolynomialSingletonClassifier x projectiveEndpoint :=
    And.intro xCarrier
      (And.intro endpointCarrier (hsame_trans xCarrier (hsame_symm endpointCarrier)))
  have endpointRows :
      forall {p : BHist}, InBundle p F ->
        PolynomialSingletonClassifier p projectiveEndpoint := by
    intro p member
    exact And.intro (locus.right member).left
      (And.intro endpointCarrier
        (hsame_trans (locus.right member).left (hsame_symm endpointCarrier)))
  exact And.intro endpointCarrier (And.intro endpointCarrier endpointRows)

def ProjectiveVarCarrier
    (endpoint chart homogeneous projective zeroEval provenance : BHist) : Prop :=
  UnaryHistory endpoint ∧ UnaryHistory chart ∧ UnaryHistory homogeneous ∧
    Cont chart homogeneous projective ∧ Cont projective zeroEval endpoint ∧
      hsame provenance endpoint

theorem ProjectiveVarCarrier_chart_homogeneous_transport
    {endpoint endpoint' chart chart' homogeneous homogeneous' projective projective' zeroEval
      provenance : BHist} :
    ProjectiveVarCarrier endpoint chart homogeneous projective zeroEval provenance ->
      hsame chart chart' -> hsame homogeneous homogeneous' ->
        Cont chart' homogeneous' projective' -> Cont projective' zeroEval endpoint' ->
          ProjectiveVarCarrier endpoint' chart' homogeneous' projective' zeroEval endpoint' ∧
            hsame projective projective' ∧ hsame endpoint endpoint' := by
  intro carrier sameChart sameHomogeneous transportedProjective transportedEndpoint
  have chartUnary : UnaryHistory chart' :=
    unary_transport carrier.right.left sameChart
  have homogeneousUnary : UnaryHistory homogeneous' :=
    unary_transport carrier.right.right.left sameHomogeneous
  have projectiveSame : hsame projective projective' :=
    cont_respects_hsame sameChart sameHomogeneous carrier.right.right.right.left
      transportedProjective
  have endpointSame : hsame endpoint endpoint' :=
    cont_respects_hsame projectiveSame (hsame_refl zeroEval)
      carrier.right.right.right.right.left transportedEndpoint
  have endpointUnary : UnaryHistory endpoint' :=
    unary_transport carrier.left endpointSame
  exact And.intro
    (And.intro endpointUnary
      (And.intro chartUnary
        (And.intro homogeneousUnary
          (And.intro transportedProjective
            (And.intro transportedEndpoint (hsame_refl endpoint'))))))
    (And.intro projectiveSame endpointSame)

theorem ProjectiveVarCarrier_scale_chart_transport
    {chart chart' point point' poly : BHist} {F : ProbeBundle BHist} :
    AffineFiniteFamilyZeroLocus (fun h : BHist => hsame h chart)
        (fun p x : BHist =>
          PolynomialSingletonClassifier (PolynomialSingletonEval x [p]) BHist.Empty)
        F point ->
      PolynomialSingletonClassifier poly BHist.Empty ->
        hsame chart chart' ->
          hsame point point' ->
            InBundle poly F ->
              AffineFiniteFamilyZeroLocus (fun h : BHist => hsame h chart')
                  (fun p x : BHist =>
                    PolynomialSingletonClassifier (PolynomialSingletonEval x [p]) BHist.Empty)
                  F point' ∧
                PolynomialSingletonClassifier (PolynomialSingletonEval point' [poly])
                  BHist.Empty := by
  intro locus polyZero sameChart samePoint polyMember
  have pointChart' : hsame point' chart' :=
    hsame_trans (hsame_symm samePoint) (hsame_trans locus.left sameChart)
  have evalPointPoly :
      PolynomialSingletonClassifier (PolynomialSingletonEval point [poly]) BHist.Empty :=
    locus.right polyMember
  have evalPointPolyParts :
      hsame poly BHist.Empty ∧ hsame (PolynomialSingletonMul point BHist.Empty) BHist.Empty :=
    append_eq_empty_iff.mp evalPointPoly.left
  have pointCarrier : PolynomialSingletonCarrier point :=
    (append_eq_empty_iff.mp evalPointPolyParts.right).left
  have point'Carrier : PolynomialSingletonCarrier point' :=
    hsame_trans (hsame_symm samePoint) pointCarrier
  have evalPoint'Poly :
      PolynomialSingletonClassifier (PolynomialSingletonEval point' [poly]) BHist.Empty := by
    have rowPoly : PolynomialSingletonClassifier (PolynomialSingletonEval point' [poly]) poly :=
      (PolynomialSingletonEval_singleton point'Carrier polyZero.left).left
    exact And.intro rowPoly.left
      (And.intro (hsame_refl BHist.Empty) (hsame_trans rowPoly.right.right polyZero.left))
  have transportedLocus :
      AffineFiniteFamilyZeroLocus (fun h : BHist => hsame h chart')
        (fun p x : BHist =>
          PolynomialSingletonClassifier (PolynomialSingletonEval x [p]) BHist.Empty)
        F point' :=
    And.intro pointChart'
      (by
        intro p memberP
        have evalPointP :
            PolynomialSingletonClassifier (PolynomialSingletonEval point [p]) BHist.Empty :=
          locus.right memberP
        have evalPointPParts :
            hsame p BHist.Empty ∧
              hsame (PolynomialSingletonMul point (PolynomialSingletonEval point []))
                BHist.Empty :=
          append_eq_empty_iff.mp evalPointP.left
        have rowP : PolynomialSingletonClassifier (PolynomialSingletonEval point' [p]) p :=
          (PolynomialSingletonEval_singleton point'Carrier evalPointPParts.left).left
        exact And.intro rowP.left
          (And.intro (hsame_refl BHist.Empty)
            (hsame_trans rowP.right.right evalPointPParts.left)))
  exact And.intro transportedLocus evalPoint'Poly

def ProjectiveVarTransportCarrier [AskSetup] [PackageSetup] (AffPoint : BHist -> Prop)
    (PolyEvalZero : BHist -> BHist -> Prop) (family : ProbeBundle BHist)
    (tokenBundle : ProbeBundle ProbeName) (chart homogeneous projective zeroEval endpoint : BHist)
    (pkg : Pkg) : Prop :=
  AffineFiniteFamilyZeroLocus AffPoint PolyEvalZero family chart ∧
    PolynomialSingletonCarrier homogeneous ∧
      UnaryHistory projective ∧
        Cont chart homogeneous endpoint ∧ hsame endpoint zeroEval ∧
          PkgSig tokenBundle endpoint pkg

theorem ProjectiveVarCarrier_obligation [AskSetup] [PackageSetup]
    {AffPoint : BHist -> Prop} {PolyEvalZero : BHist -> BHist -> Prop}
    {family : ProbeBundle BHist} {tokenBundle : ProbeBundle ProbeName}
    {chart homogeneous projective zeroEval endpoint endpoint' : BHist} {pkg : Pkg} :
    ProjectiveVarTransportCarrier AffPoint PolyEvalZero family tokenBundle chart homogeneous
        projective zeroEval endpoint pkg ->
      hsame endpoint endpoint' ->
        AffineFiniteFamilyZeroLocus AffPoint PolyEvalZero family chart ∧
          PolynomialSingletonCarrier homogeneous ∧
            UnaryHistory projective ∧
              Cont chart homogeneous endpoint' ∧ hsame endpoint' zeroEval ∧
                PkgSig tokenBundle endpoint pkg := by
  intro carrier sameEndpoint
  exact And.intro carrier.left
    (And.intro carrier.right.left
      (And.intro carrier.right.right.left
        (And.intro
          (cont_result_hsame_transport carrier.right.right.right.left sameEndpoint)
          (And.intro
            (hsame_trans (hsame_symm sameEndpoint) carrier.right.right.right.right.left)
            carrier.right.right.right.right.right))))

def ProjectiveVarVisibleCarrier [AskSetup] [PackageSetup]
    (chart homogeneous projective evaluation endpoint : BHist) (polyBundle : ProbeBundle BHist)
    (tokenBundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory chart ∧ PolynomialSingletonCarrier homogeneous ∧ UnaryHistory projective ∧
    AffineFiniteFamilyZeroLocus UnaryHistory
      (fun p x => hsame (append p x) BHist.Empty) polyBundle chart ∧
      Cont chart homogeneous evaluation ∧ TokIntro tokenBundle evaluation pkg ∧
        Cont evaluation projective endpoint

theorem ProjectiveVarVisibleCarrier_carrier_obligation [AskSetup] [PackageSetup]
    {chart homogeneous projective evaluation endpoint : BHist} {polyBundle : ProbeBundle BHist}
    {tokenBundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ProjectiveVarVisibleCarrier chart homogeneous projective evaluation endpoint polyBundle
        tokenBundle pkg ->
      UnaryHistory chart ∧ PolynomialSingletonCarrier homogeneous ∧ UnaryHistory projective ∧
        AffineFiniteFamilyZeroLocus UnaryHistory
          (fun p x => hsame (append p x) BHist.Empty) polyBundle chart ∧
          Cont chart homogeneous evaluation ∧ TokIntro tokenBundle evaluation pkg ∧
            Cont evaluation projective endpoint ∧ UnaryHistory evaluation ∧
              UnaryHistory endpoint := by
  intro carrier
  have homogeneousUnary : UnaryHistory homogeneous :=
    unary_transport unary_empty (hsame_symm carrier.right.left)
  have evaluationUnary : UnaryHistory evaluation :=
    unary_cont_closed carrier.left homogeneousUnary carrier.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed evaluationUnary carrier.right.right.left
      carrier.right.right.right.right.right.right
  exact And.intro carrier.left
    (And.intro carrier.right.left
      (And.intro carrier.right.right.left
        (And.intro carrier.right.right.right.left
          (And.intro carrier.right.right.right.right.left
            (And.intro carrier.right.right.right.right.right.left
              (And.intro carrier.right.right.right.right.right.right
                (And.intro evaluationUnary endpointUnary)))))))

end BEDC.Derived.ProjectiveVarUp
