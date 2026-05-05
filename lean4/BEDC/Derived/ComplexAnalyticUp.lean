import BEDC.Derived.ComplexUp
import BEDC.Derived.ComplexDiffUp
import BEDC.Derived.RatUp
import BEDC.Derived.RatUp.HistoryClassifier
import BEDC.FKernel.Unary.Commutativity

namespace BEDC.Derived.ComplexAnalyticUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexDiffUp
open BEDC.Derived.ComplexUp
open BEDC.Derived.ProdUp
open BEDC.Derived.RatUp

theorem ComplexAnalytic_component_continuation_witness {real imag z q zq : BHist} :
    RatHistoryCarrier real -> RatHistoryCarrier imag -> Cont real imag z -> UnaryHistory q ->
      Cont z q zq -> ∃ imagq : BHist,
        RatHistoryCarrier imagq ∧ Cont imag q imagq ∧ Cont real imagq zq ∧
          PositiveUnaryDenominator imagq := by
  intro _realCarrier imagCarrier realImag qUnary zqCont
  cases cont_assoc_middle_exists realImag zqCont with
  | intro imagq split =>
      have imagqCarrier : RatHistoryCarrier imagq :=
        RatHistoryCarrier_hsame_transport split.left.symm
          (RatHistoryCarrier_append_unary_denominator_closed imagCarrier qUnary)
      exact ⟨imagq, imagqCarrier, split.left, split.right,
        RatHistoryCarrier_iff_positive_denominator.mp imagqCarrier⟩

theorem ComplexAnalytic_component_continuation_complex_carrier {real imag z : BHist} :
    RatHistoryCarrier real -> RatHistoryCarrier imag -> Cont real imag z ->
      ComplexHistoryCarrier z := by
  intro realCarrier imagCarrier realImag
  exact ProdHistoryCarrier_cont_intro realCarrier imagCarrier realImag

def CplxExp (z w : BHist) : Prop :=
  ∃ real imag realOut imagOut : BHist,
    RatHistoryCarrier real ∧ RatHistoryCarrier imag ∧ Cont real imag z ∧
      RatHistoryCarrier realOut ∧ RatHistoryCarrier imagOut ∧ Cont realOut imagOut w ∧
        hsame realOut (append real imag) ∧ hsame imagOut (append imag real)

theorem CplxExp_component_carrier_witness {z w : BHist} :
    CplxExp z w -> ComplexHistoryCarrier z ∧ ComplexHistoryCarrier w := by
  intro expWitness
  cases expWitness with
  | intro real realData =>
      cases realData with
      | intro imag imagData =>
          cases imagData with
          | intro realOut realOutData =>
              cases realOutData with
              | intro imagOut componentData =>
                  exact And.intro
                    (ProdHistoryCarrier_cont_intro componentData.left
                      componentData.right.left componentData.right.right.left)
                    (ProdHistoryCarrier_cont_intro componentData.right.right.right.left
                      componentData.right.right.right.right.left
                      componentData.right.right.right.right.right.left)

theorem CplxExp_component_well_defined
    {real imag realOut imagOut z z' w w' : BHist} :
    RatHistoryCarrier real -> RatHistoryCarrier imag -> RatHistoryCarrier realOut ->
      RatHistoryCarrier imagOut -> Cont real imag z -> Cont real imag z' ->
        Cont realOut imagOut w -> Cont realOut imagOut w' ->
          hsame realOut (append real imag) -> hsame imagOut (append imag real) ->
            CplxExp z w ∧ CplxExp z' w' ∧
              ComplexHistoryClassifier z z' ∧ ComplexHistoryClassifier w w' := by
  intro realCarrier imagCarrier realOutCarrier imagOutCarrier contZ contZ' contW contW'
    sameRealOut sameImagOut
  have expZW : CplxExp z w :=
    Exists.intro real
      (Exists.intro imag
        (Exists.intro realOut
          (Exists.intro imagOut
            (And.intro realCarrier
              (And.intro imagCarrier
                (And.intro contZ
                  (And.intro realOutCarrier
                    (And.intro imagOutCarrier
                      (And.intro contW (And.intro sameRealOut sameImagOut))))))))))
  have expZ'W' : CplxExp z' w' :=
    Exists.intro real
      (Exists.intro imag
        (Exists.intro realOut
          (Exists.intro imagOut
            (And.intro realCarrier
              (And.intro imagCarrier
                (And.intro contZ'
                  (And.intro realOutCarrier
                    (And.intro imagOutCarrier
                      (And.intro contW' (And.intro sameRealOut sameImagOut))))))))))
  have realClassifier : RatHistoryClassifier real real :=
    And.intro realCarrier (And.intro realCarrier (hsame_refl real))
  have imagClassifier : RatHistoryClassifier imag imag :=
    And.intro imagCarrier (And.intro imagCarrier (hsame_refl imag))
  have realOutClassifier : RatHistoryClassifier realOut realOut :=
    And.intro realOutCarrier (And.intro realOutCarrier (hsame_refl realOut))
  have imagOutClassifier : RatHistoryClassifier imagOut imagOut :=
    And.intro imagOutCarrier (And.intro imagOutCarrier (hsame_refl imagOut))
  exact And.intro expZW
    (And.intro expZ'W'
      (And.intro
        (ComplexHistoryClassifier_component_classifier_intro realClassifier imagClassifier
          contZ contZ')
        (ComplexHistoryClassifier_component_classifier_intro realOutClassifier imagOutClassifier
          contW contW')))

def CplxPureImaginary (theta z : BHist) : Prop :=
  UnaryHistory theta ∧ hsame z (append (BHist.e1 BHist.Empty) (BHist.e1 theta))

def CplxPower (a s w : BHist) : Prop :=
  ComplexHistoryCarrier a ∧ ComplexHistoryCarrier s ∧ ComplexHistoryCarrier w ∧
    hsame w (append s a)

def CplxModArg (z r theta : BHist) : Prop :=
  ComplexHistoryCarrier z ∧ CplxNonZero z ∧ UnaryHistory r ∧ UnaryHistory theta ∧
    ComplexHistoryClassifier z (append (BHist.e1 r) (BHist.e1 theta))

theorem CplxPureImaginary_e1_tail_iff {theta tail : BHist} :
    CplxPureImaginary theta (BHist.e1 tail) <->
      UnaryHistory theta /\ hsame tail (append (BHist.e1 BHist.Empty) theta) := by
  constructor
  · intro pureImaginary
    exact And.intro pureImaginary.left (hsame_e1_iff.mp pureImaginary.right)
  · intro tailData
    exact And.intro tailData.left (hsame_e1_congr tailData.right)

theorem CplxPureImaginary_component_deterministic {theta theta' z : BHist} :
    CplxPureImaginary theta z -> CplxPureImaginary theta' z ->
      hsame (append (BHist.e1 BHist.Empty) (BHist.e1 theta))
        (append (BHist.e1 BHist.Empty) (BHist.e1 theta')) ∧ hsame theta theta' := by
  intro left right
  have sameComponents :
      hsame (append (BHist.e1 BHist.Empty) (BHist.e1 theta))
        (append (BHist.e1 BHist.Empty) (BHist.e1 theta')) :=
    hsame_trans (hsame_symm left.right) right.right
  have sameImaginaryE1 : hsame (BHist.e1 theta) (BHist.e1 theta') :=
    append_left_cancel (h := BHist.e1 BHist.Empty) sameComponents
  exact And.intro sameComponents (hsame_e1_iff.mp sameImaginaryE1)

theorem CplxPureImaginary_complex_carrier_witness {theta z : BHist} :
    CplxPureImaginary theta z ->
      UnaryHistory theta ∧ hsame z (append (BHist.e1 BHist.Empty) (BHist.e1 theta)) ∧
        ComplexHistoryCarrier z := by
  intro pureImaginary
  cases pureImaginary with
  | intro thetaUnary sameZ =>
      have realCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) := by
        exact RatHistoryCarrier_iff_positive_denominator.mpr
          (PositiveUnaryDenominator_e1_iff_unary.mpr unary_empty)
      have imagCarrier : RatHistoryCarrier (BHist.e1 theta) := by
        exact RatHistoryCarrier_iff_positive_denominator.mpr
          (PositiveUnaryDenominator_e1_iff_unary.mpr thetaUnary)
      have pureCarrier :
          ComplexHistoryCarrier (append (BHist.e1 BHist.Empty) (BHist.e1 theta)) := by
        exact ProdHistoryCarrier_append_intro realCarrier imagCarrier
      exact And.intro thetaUnary
        (And.intro sameZ
          (ProdHistoryCarrier_hsame_transport (hsame_symm sameZ) pureCarrier))

theorem CplxPureImaginary_hsame_transport_witness {theta z z' : BHist} :
    hsame z z' -> CplxPureImaginary theta z ->
      CplxPureImaginary theta z' ∧ hsame z' (append (BHist.e1 BHist.Empty) (BHist.e1 theta)) := by
  intro sameZZ' pureImaginary
  cases pureImaginary with
  | intro thetaUnary sameZ =>
      have sameZ' : hsame z' (append (BHist.e1 BHist.Empty) (BHist.e1 theta)) :=
        hsame_trans (hsame_symm sameZZ') sameZ
      exact And.intro (And.intro thetaUnary sameZ') sameZ'

theorem CplxPureImaginary_name_certificate :
    NameCert (fun z : BHist => exists theta : BHist, CplxPureImaginary theta z)
      hsame := by
  constructor
  · exact Exists.intro (append (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty))
      (Exists.intro BHist.Empty
        (And.intro unary_empty (hsame_refl _)))
  · intro z _source
    exact hsame_refl z
  · intro z z' sameZZ'
    exact hsame_symm sameZZ'
  · intro z z' z'' sameZZ' sameZ'Z''
    exact hsame_trans sameZZ' sameZ'Z''
  · intro z z' sameZZ' source
    cases source with
    | intro theta pureImaginary =>
        exact Exists.intro theta
          (CplxPureImaginary_hsame_transport_witness sameZZ' pureImaginary).left

theorem CplxPureImaginary_phase_stability_witness {theta phi z : BHist} :
    CplxPureImaginary theta z -> hsame theta phi ->
      CplxPureImaginary phi z ∧ UnaryHistory phi ∧
        hsame z (append (BHist.e1 BHist.Empty) (BHist.e1 phi)) := by
  intro pureImaginary sameThetaPhi
  cases pureImaginary with
  | intro thetaUnary sameZ =>
      have phiUnary : UnaryHistory phi := unary_transport thetaUnary sameThetaPhi
      have sameZPhi : hsame z (append (BHist.e1 BHist.Empty) (BHist.e1 phi)) := by
        cases sameThetaPhi
        exact sameZ
      exact And.intro (And.intro phiUnary sameZPhi) (And.intro phiUnary sameZPhi)

theorem CplxPureImaginary_empty_absurd {theta : BHist} :
    CplxPureImaginary theta BHist.Empty -> False := by
  intro pureImaginary
  exact ComplexHistoryCarrier_not_empty
    (CplxPureImaginary_complex_carrier_witness pureImaginary).right.right (hsame_refl BHist.Empty)

theorem CplxPureImaginary_empty_continuation_absurd {theta z q : BHist} :
    CplxPureImaginary theta z -> Cont z q BHist.Empty -> False := by
  intro pureImaginary emptyCont
  have sourceEmpty : hsame z BHist.Empty := (append_eq_empty_iff.mp emptyCont.symm).left
  exact CplxPureImaginary_empty_absurd
    (CplxPureImaginary_hsame_transport_witness sourceEmpty pureImaginary).left

theorem CplxPureImaginary_component_continuation_witness {theta z q zq : BHist} :
    CplxPureImaginary theta z -> UnaryHistory q -> Cont z q zq ->
      ∃ imagq : BHist,
        RatHistoryCarrier imagq ∧ Cont (BHist.e1 theta) q imagq ∧
          Cont (BHist.e1 BHist.Empty) imagq zq ∧ PositiveUnaryDenominator imagq := by
  intro pureImaginary qUnary zqCont
  cases pureImaginary with
  | intro thetaUnary sameZ =>
      have realCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) := by
        exact RatHistoryCarrier_iff_positive_denominator.mpr
          (PositiveUnaryDenominator_e1_iff_unary.mpr unary_empty)
      have imagCarrier : RatHistoryCarrier (BHist.e1 theta) := by
        exact RatHistoryCarrier_iff_positive_denominator.mpr
          (PositiveUnaryDenominator_e1_iff_unary.mpr thetaUnary)
      exact
        ComplexAnalytic_component_continuation_witness realCarrier imagCarrier sameZ qUnary zqCont

theorem CplxPureImaginary_suffix_component_tail_witness {theta z q zq : BHist} :
    CplxPureImaginary theta z -> UnaryHistory q -> Cont z q zq ->
      ∃ imagq : BHist,
        RatHistoryCarrier imagq ∧ hsame imagq (BHist.e1 (append theta q)) ∧
          Cont (BHist.e1 BHist.Empty) imagq zq ∧ PositiveUnaryDenominator imagq := by
  intro pureImaginary qUnary zqCont
  cases CplxPureImaginary_component_continuation_witness pureImaginary qUnary zqCont with
  | intro imagq data =>
      have sameTail : hsame imagq (BHist.e1 (append theta q)) :=
        data.right.left.trans (unary_append_e1_left (h := q) (k := theta) qUnary)
      exact ⟨imagq, data.left, sameTail, data.right.right.left, data.right.right.right⟩

theorem CplxPureImaginary_suffix_parameter_readback {theta psi z q zq : BHist} :
    CplxPureImaginary theta z -> UnaryHistory q -> Cont z q zq ->
      CplxPureImaginary psi zq -> hsame psi (append theta q) := by
  intro pureTheta qUnary zqCont purePsi
  cases CplxPureImaginary_suffix_component_tail_witness pureTheta qUnary zqCont with
  | intro imagq data =>
      have displayedCont :
          Cont (BHist.e1 BHist.Empty) imagq
            (append (BHist.e1 BHist.Empty) (BHist.e1 psi)) :=
        cont_result_hsame_transport data.right.right.left purePsi.right
      have sameImaginaryDisplay : hsame (BHist.e1 psi) imagq :=
        append_left_cancel (h := BHist.e1 BHist.Empty) displayedCont
      exact hsame_e1_iff.mp (hsame_trans sameImaginaryDisplay data.right.left)

theorem CplxPureImaginary_suffix_continuation_complex_carrier {theta z q zq : BHist} :
    CplxPureImaginary theta z -> UnaryHistory q -> Cont z q zq ->
      ComplexHistoryCarrier zq ∧ (hsame zq BHist.Empty -> False) := by
  intro pureImaginary qUnary zqCont
  cases CplxPureImaginary_component_continuation_witness pureImaginary qUnary zqCont with
  | intro imagq split =>
      have realCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) := by
        exact RatHistoryCarrier_iff_positive_denominator.mpr
          (PositiveUnaryDenominator_e1_iff_unary.mpr unary_empty)
      have zqCarrier : ComplexHistoryCarrier zq :=
        ComplexAnalytic_component_continuation_complex_carrier realCarrier split.left
          split.right.right.left
      exact And.intro zqCarrier (ComplexHistoryCarrier_not_empty zqCarrier)

theorem CplxPureImaginary_suffix_continuation_classifier {theta phi z w q q' zq wq : BHist} :
    CplxPureImaginary theta z -> CplxPureImaginary phi w -> hsame theta phi ->
      UnaryHistory q -> hsame q q' -> Cont z q zq -> Cont w q' wq ->
        ComplexHistoryClassifier zq wq := by
  intro pureTheta purePhi sameThetaPhi qUnary sameQQ' contZ contW
  cases CplxPureImaginary_component_continuation_witness pureTheta qUnary contZ with
  | intro imagq leftData =>
      have qUnary' : UnaryHistory q' := unary_transport qUnary sameQQ'
      cases CplxPureImaginary_component_continuation_witness purePhi qUnary' contW with
      | intro imagq' rightData =>
          have thetaUnary : UnaryHistory theta := pureTheta.left
          have phiUnary : UnaryHistory phi := purePhi.left
          have realClassifier :
              RatHistoryClassifier (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty) :=
            RatHistoryClassifier_e1_tail_unary_iff.mpr
              ⟨unary_empty, unary_empty, hsame_refl BHist.Empty⟩
          have baseImagClassifier :
              RatHistoryClassifier (BHist.e1 theta) (BHist.e1 phi) :=
            RatHistoryClassifier_e1_tail_unary_iff.mpr
              ⟨thetaUnary, phiUnary, sameThetaPhi⟩
          have continuedImagClassifier :
              RatHistoryClassifier (append (BHist.e1 theta) q) (append (BHist.e1 phi) q') :=
            RatHistoryClassifier_append_unary_denominator_closed baseImagClassifier qUnary
              sameQQ'
          have imagClassifier : RatHistoryClassifier imagq imagq' :=
            RatHistoryClassifier_hsame_transport leftData.right.left.symm
              rightData.right.left.symm continuedImagClassifier
          exact ComplexHistoryClassifier_component_classifier_intro realClassifier imagClassifier
            leftData.right.right.left rightData.right.right.left

theorem CplxPureImaginary_continuation_complex_carrier {theta z q zq : BHist} :
    CplxPureImaginary theta z -> UnaryHistory q -> Cont z q zq ->
      ComplexHistoryCarrier zq := by
  intro pureImaginary qUnary zqCont
  cases CplxPureImaginary_component_continuation_witness pureImaginary qUnary zqCont with
  | intro imagq data =>
      have realCarrier : RatHistoryCarrier (BHist.e1 BHist.Empty) := by
        exact RatHistoryCarrier_iff_positive_denominator.mpr
          (PositiveUnaryDenominator_e1_iff_unary.mpr unary_empty)
      exact ProdHistoryCarrier_cont_intro realCarrier data.left data.right.right.left

theorem CplxPureImaginary_component_continuation_complex_carrier {theta z q zq : BHist} :
    CplxPureImaginary theta z -> UnaryHistory q -> Cont z q zq ->
      ComplexHistoryCarrier zq := by
  exact CplxPureImaginary_continuation_complex_carrier

theorem CplxPureImaginary_continuation_e0_result_absurd {theta z q tail : BHist} :
    CplxPureImaginary theta z -> UnaryHistory q -> Cont z q (BHist.e0 tail) -> False := by
  intro pureImaginary qUnary zqCont
  have resultCarrier : ComplexHistoryCarrier (BHist.e0 tail) :=
    CplxPureImaginary_continuation_complex_carrier pureImaginary qUnary zqCont
  exact unary_no_zero_extension (ComplexHistoryCarrier_unary resultCarrier)

theorem CplxPureImaginary_witness_unique {theta phi z : BHist} :
    (UnaryHistory theta ∧ hsame z (append (BHist.e1 BHist.Empty) (BHist.e1 theta))) ->
      (UnaryHistory phi ∧ hsame z (append (BHist.e1 BHist.Empty) (BHist.e1 phi))) ->
        hsame theta phi := by
  intro left right
  have sameAnchors :
      hsame (append (BHist.e1 BHist.Empty) (BHist.e1 theta))
        (append (BHist.e1 BHist.Empty) (BHist.e1 phi)) :=
    hsame_trans (hsame_symm left.right) right.right
  exact hsame_e1_iff.mp (append_left_cancel (h := BHist.e1 BHist.Empty) sameAnchors)

theorem CplxPureImaginary_suffix_source_deterministic {theta phi z w q zq : BHist} :
    CplxPureImaginary theta z -> CplxPureImaginary phi w -> Cont z q zq ->
      Cont w q zq -> hsame theta phi := by
  intro pureTheta purePhi zCont wCont
  have sameZW : hsame z w := cont_right_cancel zCont wCont
  have purePhiAtZ : CplxPureImaginary phi z :=
    (CplxPureImaginary_hsame_transport_witness (hsame_symm sameZW) purePhi).left
  exact CplxPureImaginary_witness_unique pureTheta purePhiAtZ

theorem CplxPureImaginary_suffix_tail_deterministic {theta phi z w q q' zq wq : BHist} :
    CplxPureImaginary theta z -> CplxPureImaginary phi w -> hsame theta phi ->
      Cont z q zq -> Cont w q' wq -> hsame zq wq -> hsame q q' := by
  intro pureTheta purePhi sameThetaPhi zCont wCont sameResult
  have sameAnchors :
      hsame (append (BHist.e1 BHist.Empty) (BHist.e1 theta))
        (append (BHist.e1 BHist.Empty) (BHist.e1 phi)) := by
    cases sameThetaPhi
    rfl
  have sameZW : hsame z w :=
    hsame_trans pureTheta.right (hsame_trans sameAnchors (hsame_symm purePhi.right))
  cases sameZW
  exact append_left_cancel (h := z) (zCont.symm.trans (sameResult.trans wCont))

theorem complex_analytic_licensed_not_primitive :
    SemanticNameCert
      (fun z : BHist => exists theta : BHist, CplxPureImaginary theta z)
      (fun z : BHist => exists theta : BHist, CplxPureImaginary theta z)
      (fun z : BHist => exists theta : BHist, CplxPureImaginary theta z)
      (fun z z' : BHist =>
        (exists theta : BHist, CplxPureImaginary theta z) ∧
          (exists theta : BHist, CplxPureImaginary theta z') ∧ hsame z z') := by
  exact {
    core := {
      carrier_inhabited :=
        BEDC.FKernel.NameCert.NameCert.carrier_inhabited CplxPureImaginary_name_certificate
      equiv_refl := by
        intro z source
        exact And.intro source (And.intro source (hsame_refl z))
      equiv_symm := by
        intro z z' classified
        exact And.intro classified.right.left
          (And.intro classified.left (hsame_symm classified.right.right))
      equiv_trans := by
        intro z z' z'' leftClass rightClass
        exact And.intro leftClass.left
          (And.intro rightClass.right.left
            (hsame_trans leftClass.right.right rightClass.right.right))
      carrier_respects_equiv := by
        intro z z' classified _source
        exact classified.right.left
    }
    pattern_sound := by
      intro z source
      exact source
    ledger_sound := by
      intro z source
      exact source
  }

end BEDC.Derived.ComplexAnalyticUp
