import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem DiffFormBHistCarrier_coordinate_ledger
    {degree probe tensor scalar antisym ledger : BHist}
    (degreeUnary : UnaryHistory degree) (probeUnary : UnaryHistory probe)
    (tensorRoute : Cont degree probe tensor)
    (antisymUnary : UnaryHistory antisym)
    (scalarRoute : Cont tensor antisym scalar)
    (ledgerRoute : hsame ledger (append degree (append probe (append tensor (append scalar antisym))))) :
    UnaryHistory degree ∧ UnaryHistory probe ∧ UnaryHistory tensor ∧ UnaryHistory scalar ∧
      hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) := by
  have tensorUnary : UnaryHistory tensor := by
    cases tensorRoute
    exact unary_append_closed degreeUnary probeUnary
  have scalarUnary : UnaryHistory scalar := by
    cases scalarRoute
    exact unary_append_closed tensorUnary antisymUnary
  exact ⟨degreeUnary, probeUnary, tensorUnary, scalarUnary, ledgerRoute⟩

def DiffFormBHistClassifier
    (ScalarClassifier : BHist -> BHist -> Prop) (probes : ProbeBundle BHist)
    (degree probe tensor scalar antisym ledger degree' probe' tensor' scalar' antisym'
      ledger' : BHist) : Prop :=
  InBundle probe probes ∧ InBundle probe' probes ∧ hsame degree degree' ∧
    hsame probe probe' ∧ hsame tensor tensor' ∧ ScalarClassifier scalar scalar' ∧
      hsame antisym antisym' ∧ hsame ledger ledger'

theorem DiffFormBHistClassifier_symmetry_obligation
    {ScalarCarrier : BHist -> Prop} {ScalarClassifier : BHist -> BHist -> Prop}
    (scalarCert : NameCert ScalarCarrier ScalarClassifier)
    {probes : ProbeBundle BHist}
    {d p t s a l d' p' t' s' a' l' : BHist} :
    DiffFormBHistClassifier ScalarClassifier probes d p t s a l d' p' t' s' a' l' ->
      DiffFormBHistClassifier ScalarClassifier probes d' p' t' s' a' l' d p t s a l := by
  intro rows
  exact And.intro rows.right.left
    (And.intro rows.left
      (And.intro (hsame_symm rows.right.right.left)
        (And.intro (hsame_symm rows.right.right.right.left)
          (And.intro (hsame_symm rows.right.right.right.right.left)
            (And.intro (NameCert.equiv_symm scalarCert rows.right.right.right.right.right.left)
              (And.intro (hsame_symm rows.right.right.right.right.right.right.left)
                (hsame_symm rows.right.right.right.right.right.right.right)))))))

theorem DiffFormBHistClassifier_transitivity_obligation
    {ScalarCarrier : BHist -> Prop} {ScalarClassifier : BHist -> BHist -> Prop}
    (scalarCert : NameCert ScalarCarrier ScalarClassifier)
    {probes : ProbeBundle BHist}
    {d p t s a l d' p' t' s' a' l' d'' p'' t'' s'' a'' l'' : BHist} :
    DiffFormBHistClassifier ScalarClassifier probes d p t s a l d' p' t' s' a' l' ->
      DiffFormBHistClassifier ScalarClassifier probes d' p' t' s' a' l' d'' p'' t'' s'' a'' l'' ->
        DiffFormBHistClassifier ScalarClassifier probes d p t s a l d'' p'' t'' s'' a'' l'' := by
  intro leftRows rightRows
  exact And.intro leftRows.left
    (And.intro rightRows.right.left
      (And.intro (hsame_trans leftRows.right.right.left rightRows.right.right.left)
        (And.intro (hsame_trans leftRows.right.right.right.left rightRows.right.right.right.left)
          (And.intro
            (hsame_trans leftRows.right.right.right.right.left
              rightRows.right.right.right.right.left)
            (And.intro
              (NameCert.equiv_trans scalarCert leftRows.right.right.right.right.right.left
                rightRows.right.right.right.right.right.left)
              (And.intro
                (hsame_trans leftRows.right.right.right.right.right.right.left
                  rightRows.right.right.right.right.right.right.left)
                (hsame_trans leftRows.right.right.right.right.right.right.right
                  rightRows.right.right.right.right.right.right.right)))))))

theorem DiffFormExteriorDerivative_degree_raise_ledger
    {degree probe tensor scalar antisym ledger targetDegree : BHist} :
    UnaryHistory degree -> UnaryHistory probe -> Cont degree probe tensor ->
      UnaryHistory antisym -> Cont tensor antisym scalar ->
        hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ->
          Cont degree (BHist.e1 BHist.Empty) targetDegree ->
            UnaryHistory degree ∧ UnaryHistory targetDegree ∧
              Cont degree (BHist.e1 BHist.Empty) targetDegree ∧ UnaryHistory tensor ∧
                UnaryHistory scalar := by
  intro degreeUnary probeUnary tensorRoute antisymUnary scalarRoute ledgerRoute targetRoute
  have coordinateRows :=
    DiffFormBHistCarrier_coordinate_ledger degreeUnary probeUnary tensorRoute antisymUnary
      scalarRoute ledgerRoute
  have targetUnary : UnaryHistory targetDegree :=
    unary_cont_closed degreeUnary (unary_e1_closed unary_empty) targetRoute
  exact ⟨coordinateRows.left, targetUnary, targetRoute, coordinateRows.right.right.left,
    coordinateRows.right.right.right.left⟩

def DiffFormExteriorDerivativeLedger
    (omega domega d dplus probe probe' tensor tensor' scalar scalar' antisym source :
      BHist) :
    Prop :=
  UnaryHistory omega ∧ UnaryHistory domega ∧ UnaryHistory d ∧ UnaryHistory dplus ∧
    Cont d (BHist.e1 BHist.Empty) dplus ∧ hsame probe probe' ∧ hsame tensor tensor' ∧
      hsame scalar scalar' ∧ UnaryHistory antisym ∧ UnaryHistory source

theorem DiffFormExteriorDerivativeLedger_degree_raise
    {omega domega d dplus probe probe' tensor tensor' scalar scalar' antisym source : BHist} :
    DiffFormExteriorDerivativeLedger omega domega d dplus probe probe' tensor tensor' scalar
      scalar' antisym source ->
      UnaryHistory d ∧ UnaryHistory dplus ∧ Cont d (BHist.e1 BHist.Empty) dplus := by
  intro ledger
  exact And.intro ledger.right.right.left
    (And.intro ledger.right.right.right.left ledger.right.right.right.right.left)

theorem DiffFormExteriorDerivativeLedger_hsame_transport_degree_raise
    {omega domega d dplus probe probe' tensor tensor' scalar scalar' antisym source omega2
      domega2 d2 dplus2 probe2 probe2' tensor2 tensor2' scalar2 scalar2' antisym2 source2 :
      BHist} :
    hsame omega omega2 -> hsame domega domega2 -> hsame d d2 -> hsame dplus dplus2 ->
      hsame probe probe2 -> hsame probe' probe2' -> hsame tensor tensor2 ->
        hsame tensor' tensor2' -> hsame scalar scalar2 -> hsame scalar' scalar2' ->
          hsame antisym antisym2 -> hsame source source2 ->
            DiffFormExteriorDerivativeLedger omega domega d dplus probe probe' tensor tensor'
              scalar scalar' antisym source ->
              DiffFormExteriorDerivativeLedger omega2 domega2 d2 dplus2 probe2 probe2'
                tensor2 tensor2' scalar2 scalar2' antisym2 source2 ∧ UnaryHistory d2 ∧
                  UnaryHistory dplus2 ∧ Cont d2 (BHist.e1 BHist.Empty) dplus2 := by
  intro sameOmega sameDomega sameDegree sameRaised sameProbe sameProbe' sameTensor
    sameTensor' sameScalar sameScalar' sameAntisym sameSource ledger
  cases sameOmega
  cases sameDomega
  cases sameDegree
  cases sameRaised
  cases sameProbe
  cases sameProbe'
  cases sameTensor
  cases sameTensor'
  cases sameScalar
  cases sameScalar'
  cases sameAntisym
  cases sameSource
  exact And.intro ledger (DiffFormExteriorDerivativeLedger_degree_raise ledger)

theorem DiffFormExteriorDerivative_scalar_transport_boundary
    {ScalarClassifier : BHist -> BHist -> Prop} {probes : ProbeBundle BHist}
    {degree probe tensor scalar antisym ledger degree' probe' tensor' scalar' antisym'
      ledger' : BHist} :
    DiffFormBHistClassifier ScalarClassifier probes degree probe tensor scalar antisym ledger degree'
      probe' tensor' scalar' antisym' ledger' ->
      ScalarClassifier scalar scalar' ∧ hsame ledger ledger' := by
  intro classified
  exact And.intro
    classified.right.right.right.right.right.left
    classified.right.right.right.right.right.right.right

theorem DiffFormExteriorDerivativeLedger_classifier_transport
    {probes : ProbeBundle BHist}
    {omega domega d dplus probe probe' tensor tensor' scalar scalar' antisym source
      omega2 domega2 d2 dplus2 probe2 probe2' tensor2 tensor2' scalar2 scalar2'
      antisym2 source2 : BHist} :
    DiffFormExteriorDerivativeLedger omega domega d dplus probe probe' tensor tensor'
      scalar scalar' antisym source ->
    DiffFormBHistClassifier hsame probes d probe tensor scalar antisym source
      d2 probe2 tensor2 scalar2 antisym2 source2 ->
    hsame omega omega2 -> hsame domega domega2 -> hsame d d2 -> hsame dplus dplus2 ->
    hsame probe' probe2' -> hsame tensor' tensor2' -> hsame scalar' scalar2' ->
      DiffFormExteriorDerivativeLedger omega2 domega2 d2 dplus2 probe2 probe2'
        tensor2 tensor2' scalar2 scalar2' antisym2 source2 := by
  intro ledger classified sameOmega sameDomega sameD sameDplus sameProbe' sameTensor'
    sameScalar'
  have omegaUnary : UnaryHistory omega2 := unary_transport ledger.left sameOmega
  have domegaUnary : UnaryHistory domega2 := unary_transport ledger.right.left sameDomega
  have dUnary : UnaryHistory d2 := unary_transport ledger.right.right.left sameD
  have dplusUnary : UnaryHistory dplus2 :=
    unary_transport ledger.right.right.right.left sameDplus
  have degreeCont : Cont d2 (BHist.e1 BHist.Empty) dplus2 := by
    cases sameD
    cases sameDplus
    exact ledger.right.right.right.right.left
  have probeSame : hsame probe2 probe2' :=
    hsame_trans (hsame_symm classified.right.right.right.left)
      (hsame_trans ledger.right.right.right.right.right.left sameProbe')
  have tensorSame : hsame tensor2 tensor2' :=
    hsame_trans (hsame_symm classified.right.right.right.right.left)
      (hsame_trans ledger.right.right.right.right.right.right.left sameTensor')
  have scalarSame : hsame scalar2 scalar2' :=
    hsame_trans (hsame_symm classified.right.right.right.right.right.left)
      (hsame_trans ledger.right.right.right.right.right.right.right.left sameScalar')
  have antisymUnary : UnaryHistory antisym2 :=
    unary_transport ledger.right.right.right.right.right.right.right.right.left
      classified.right.right.right.right.right.right.left
  have sourceUnary : UnaryHistory source2 :=
    unary_transport ledger.right.right.right.right.right.right.right.right.right
      classified.right.right.right.right.right.right.right
  exact And.intro omegaUnary
    (And.intro domegaUnary
      (And.intro dUnary
        (And.intro dplusUnary
          (And.intro degreeCont
            (And.intro probeSame
              (And.intro tensorSame
                (And.intro scalarSame
                  (And.intro antisymUnary sourceUnary))))))))

inductive DegreeProbeAligned : BHist -> ProbeBundle BHist -> Prop where
  | nil : DegreeProbeAligned BHist.Empty ProbeBundle.Bnil
  | cons {d : BHist} {p : BHist} {ps : ProbeBundle BHist} :
      DegreeProbeAligned d ps -> DegreeProbeAligned (BHist.e1 d) (ProbeBundle.Bcons p ps)

private theorem DiffFormDegreeProbeAligned_bundleAppend_cont_unary
    {d : BHist} {bundle : ProbeBundle BHist} :
    DegreeProbeAligned d bundle -> UnaryHistory d := by
  intro aligned
  induction aligned with
  | nil =>
      exact unary_empty
  | cons tailAligned ih =>
      exact unary_e1_closed ih

private theorem DiffFormDegreeProbeAligned_bundleAppend_cont_transport
    {d d' : BHist} {bundle : ProbeBundle BHist} :
    DegreeProbeAligned d bundle -> hsame d d' -> DegreeProbeAligned d' bundle := by
  intro aligned sameDegree
  cases sameDegree
  exact aligned

private theorem DiffFormDegreeProbeAligned_bundleAppend_cont_append
    {d e : BHist} {left right : ProbeBundle BHist} :
    DegreeProbeAligned d left -> DegreeProbeAligned e right ->
      DegreeProbeAligned (append e d) (bundleAppend left right) := by
  intro leftAligned rightAligned
  induction leftAligned with
  | nil =>
      exact rightAligned
  | cons tailAligned ih =>
      exact DegreeProbeAligned.cons ih

theorem DiffFormDegreeProbeAligned_bundleAppend_cont
    {d e out : BHist} {left right : ProbeBundle BHist} :
    DegreeProbeAligned d left -> DegreeProbeAligned e right -> Cont d e out ->
      DegreeProbeAligned out (bundleAppend left right) := by
  intro leftAligned rightAligned route
  cases route
  have leftUnary : UnaryHistory d :=
    DiffFormDegreeProbeAligned_bundleAppend_cont_unary leftAligned
  have rightUnary : UnaryHistory e :=
    DiffFormDegreeProbeAligned_bundleAppend_cont_unary rightAligned
  exact DiffFormDegreeProbeAligned_bundleAppend_cont_transport
    (DiffFormDegreeProbeAligned_bundleAppend_cont_append leftAligned rightAligned)
    (unary_append_comm_hsame rightUnary leftUnary)

end BEDC.Derived.DiffFormUp
