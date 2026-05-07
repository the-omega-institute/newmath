import BEDC.Derived.CategoryUp
import BEDC.Derived.GroupUp
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Units
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.AbelianCatUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp
open BEDC.Derived.GroupUp

def AbelianCatKernelCokernelCarrier
    (obj hom zero biprod add kernel cokernel factor : BHist) : Prop :=
  UnaryHistory obj ∧
    UnaryHistory hom ∧
      CategoryHomCarrier obj obj hom ∧
        GroupSingletonCarrier zero ∧
          Cont BHist.Empty hom biprod ∧
            Cont hom BHist.Empty add ∧
              Cont hom zero kernel ∧ Cont zero hom cokernel ∧ Cont kernel cokernel factor

theorem AbelianCatKernelCokernelCarrier_factorization_rows
    {obj hom zero biprod add kernel cokernel factor : BHist} :
    AbelianCatKernelCokernelCarrier obj hom zero biprod add kernel cokernel factor ->
      CategoryHomCarrier obj obj hom ∧
        Cont hom zero kernel ∧
          Cont zero hom cokernel ∧ Cont kernel cokernel factor ∧ UnaryHistory factor := by
  intro carrier
  have homUnary : UnaryHistory hom := carrier.right.left
  have zeroUnary : UnaryHistory zero :=
    unary_transport unary_empty (hsame_symm carrier.right.right.right.left)
  have kernelUnary : UnaryHistory kernel :=
    unary_cont_closed homUnary zeroUnary carrier.right.right.right.right.right.right.left
  have cokernelUnary : UnaryHistory cokernel :=
    unary_cont_closed zeroUnary homUnary carrier.right.right.right.right.right.right.right.left
  have factorUnary : UnaryHistory factor :=
    unary_cont_closed kernelUnary cokernelUnary carrier.right.right.right.right.right.right.right.right
  exact And.intro carrier.right.right.left
    (And.intro carrier.right.right.right.right.right.right.left
      (And.intro carrier.right.right.right.right.right.right.right.left
        (And.intro carrier.right.right.right.right.right.right.right.right factorUnary)))

theorem AbelianCatKernelCokernelCarrier_zero_biproduct_readback
    {obj hom zero biprod add kernel cokernel factor : BHist} :
    AbelianCatKernelCokernelCarrier obj hom zero biprod add kernel cokernel factor ->
      GroupSingletonCarrier zero ∧ Cont BHist.Empty hom biprod ∧ Cont hom BHist.Empty add ∧
        hsame biprod hom ∧ hsame add hom ∧ UnaryHistory biprod ∧ UnaryHistory add := by
  intro carrier
  have homUnary : UnaryHistory hom := carrier.right.left
  have zeroCarrier : GroupSingletonCarrier zero := carrier.right.right.right.left
  have biprodRow : Cont BHist.Empty hom biprod := carrier.right.right.right.right.left
  have addRow : Cont hom BHist.Empty add := carrier.right.right.right.right.right.left
  have biprodHom : hsame biprod hom := cont_left_unit_result biprodRow
  have addHom : hsame add hom := cont_right_unit_result addRow
  have biprodUnary : UnaryHistory biprod := unary_transport homUnary (hsame_symm biprodHom)
  have addUnary : UnaryHistory add := unary_transport homUnary (hsame_symm addHom)
  exact And.intro zeroCarrier
    (And.intro biprodRow
      (And.intro addRow
        (And.intro biprodHom (And.intro addHom (And.intro biprodUnary addUnary)))))

def AbelianCatAdditiveCarrier
    (source target zero add kernel cokernel factor : BHist) : Prop :=
  CategoryHomCarrier source target zero ∧ GroupSingletonCarrier add ∧ UnaryHistory kernel ∧
    UnaryHistory cokernel ∧ UnaryHistory factor ∧ Cont zero add kernel ∧
      Cont kernel cokernel factor

def AbelianCatAdditiveClassifier
    (source target zero add kernel cokernel factor source' target' zero' add' kernel' cokernel'
      factor' : BHist) : Prop :=
  hsame source source' ∧ hsame target target' ∧ hsame zero zero' ∧ hsame add add' ∧
    hsame kernel kernel' ∧ hsame cokernel cokernel' ∧ hsame factor factor'

theorem AbelianCatAdditiveCarrier_classifier_transport
    {source target zero add kernel cokernel factor source' target' zero' add' kernel' cokernel'
      factor' : BHist} :
    AbelianCatAdditiveCarrier source target zero add kernel cokernel factor ->
      AbelianCatAdditiveClassifier source target zero add kernel cokernel factor source' target'
        zero' add' kernel' cokernel' factor' ->
        AbelianCatAdditiveCarrier source' target' zero' add' kernel' cokernel' factor' ∧
          CategoryHomCarrier source' target' zero' ∧ GroupSingletonCarrier add' ∧
            Cont zero' add' kernel' ∧ Cont kernel' cokernel' factor' := by
  intro carrier classified
  have sourceSame : hsame source source' := classified.left
  have targetSame : hsame target target' := classified.right.left
  have zeroSame : hsame zero zero' := classified.right.right.left
  have homCarrier : CategoryHomCarrier source' target' zero' :=
    CategoryHomCarrier_hsame_transport sourceSame targetSame zeroSame carrier.left
  cases sourceSame
  cases targetSame
  cases zeroSame
  cases classified.right.right.right.left
  cases classified.right.right.right.right.left
  cases classified.right.right.right.right.right.left
  cases classified.right.right.right.right.right.right
  exact And.intro carrier
    (And.intro homCarrier
      (And.intro carrier.right.left
        (And.intro carrier.right.right.right.right.right.left
          carrier.right.right.right.right.right.right)))

theorem AbelianCatAdditiveCarrier_additive_readback
    {source target zero add kernel cokernel factor : BHist} :
    AbelianCatAdditiveCarrier source target zero add kernel cokernel factor ->
      hsame kernel zero ∧ CategoryHomCarrier source target zero ∧ GroupSingletonCarrier add ∧
        Cont kernel cokernel factor ∧ UnaryHistory kernel ∧ UnaryHistory factor := by
  intro carrier
  have zeroCarrier : CategoryHomCarrier source target zero := carrier.left
  have addSingleton : GroupSingletonCarrier add := carrier.right.left
  have kernelUnary : UnaryHistory kernel := carrier.right.right.left
  have factorUnary : UnaryHistory factor := carrier.right.right.right.right.left
  have kernelRow : Cont zero add kernel := carrier.right.right.right.right.right.left
  have factorRow : Cont kernel cokernel factor := carrier.right.right.right.right.right.right
  have kernelZero : hsame kernel zero :=
    cont_respects_hsame (hsame_refl zero) addSingleton kernelRow (cont_right_unit zero)
  exact And.intro kernelZero
    (And.intro zeroCarrier
      (And.intro addSingleton
        (And.intro factorRow (And.intro kernelUnary factorUnary))))

theorem AbelianCatAdditiveCarrier_zero_biproduct_rows
    {source target zero add kernel cokernel factor : BHist} :
    AbelianCatAdditiveCarrier source target zero add kernel cokernel factor ->
      CategoryHomCarrier source target zero ∧ GroupSingletonCarrier add ∧
        Cont zero add kernel ∧ hsame kernel (append zero add) ∧ Cont kernel cokernel factor ∧
          hsame factor (append (append zero add) cokernel) := by
  intro carrier
  have zeroAddRow : Cont zero add kernel := carrier.right.right.right.right.right.left
  have factorRow : Cont kernel cokernel factor := carrier.right.right.right.right.right.right
  exact And.intro carrier.left
      (And.intro carrier.right.left
        (And.intro zeroAddRow
          (And.intro zeroAddRow
            (And.intro factorRow
              (hsame_trans factorRow (congrArg (fun h => append h cokernel) zeroAddRow))))))

theorem AbelianCatAdditiveCarrier_zero_additive_kernel_boundary
    {source target zero add kernel cokernel factor zeroAdd : BHist} :
    AbelianCatAdditiveCarrier source target zero add kernel cokernel factor ->
      Cont zero add zeroAdd ->
        CategoryHomCarrier source target zero ∧ GroupSingletonCarrier add ∧
          UnaryHistory zeroAdd ∧ Cont zero add zeroAdd ∧ Cont zeroAdd cokernel factor := by
  intro carrier zeroAddRow
  have homCarrier : CategoryHomCarrier source target zero := carrier.left
  have addCarrier : GroupSingletonCarrier add := carrier.right.left
  have zeroUnary : UnaryHistory zero := homCarrier.right.right.left
  have addUnary : UnaryHistory add := unary_transport unary_empty (hsame_symm addCarrier)
  have zeroAddUnary : UnaryHistory zeroAdd :=
    unary_cont_closed zeroUnary addUnary zeroAddRow
  have kernelRow : Cont zero add kernel := carrier.right.right.right.right.right.left
  have sameZeroAddKernel : hsame zeroAdd kernel :=
    cont_deterministic zeroAddRow kernelRow
  have factorRow : Cont kernel cokernel factor := carrier.right.right.right.right.right.right
  have transportedFactor : Cont zeroAdd cokernel factor :=
    cont_hsame_transport (hsame_symm sameZeroAddKernel) (hsame_refl cokernel)
      (hsame_refl factor) factorRow
  exact And.intro homCarrier
    (And.intro addCarrier
      (And.intro zeroAddUnary (And.intro zeroAddRow transportedFactor)))

theorem AbelianCatAdditiveCarrier_factor_unary_closure
    {source target zero add kernel cokernel factor : BHist} :
    AbelianCatAdditiveCarrier source target zero add kernel cokernel factor ->
      UnaryHistory factor ∧ hsame factor (append kernel cokernel) := by
  intro carrier
  exact And.intro carrier.right.right.right.right.left carrier.right.right.right.right.right.right

theorem AbelianCatAdditiveCarrier_factor_append_readback
    {source target zero add kernel cokernel factor : BHist} :
    AbelianCatAdditiveCarrier source target zero add kernel cokernel factor ->
      hsame factor (append (append zero add) cokernel) ∧
        Cont (append zero add) cokernel factor ∧ UnaryHistory factor := by
  intro carrier
  have factorUnary : UnaryHistory factor := carrier.right.right.right.right.left
  have kernelRow : Cont zero add kernel := carrier.right.right.right.right.right.left
  have factorRow : Cont kernel cokernel factor := carrier.right.right.right.right.right.right
  have factorAppend : hsame factor (append (append zero add) cokernel) := by
    cases kernelRow
    exact factorRow
  have composedRow : Cont (append zero add) cokernel factor := by
    cases kernelRow
    exact factorRow
  exact And.intro factorAppend (And.intro composedRow factorUnary)

theorem AbelianCatKernelCokernel_visible_factorization
    {f kerObj cokObj imageObj coimageObj comparison recomposed : BHist} :
    hsame f BHist.Empty -> Cont BHist.Empty f kerObj -> Cont f BHist.Empty cokObj ->
      Cont kerObj cokObj imageObj -> Cont imageObj BHist.Empty coimageObj ->
        Cont coimageObj BHist.Empty comparison -> Cont comparison BHist.Empty recomposed ->
          hsame kerObj BHist.Empty ∧ hsame cokObj BHist.Empty ∧
            hsame imageObj BHist.Empty ∧ hsame coimageObj BHist.Empty ∧
              hsame comparison BHist.Empty ∧ hsame recomposed f ∧ UnaryHistory kerObj ∧
                UnaryHistory cokObj ∧ UnaryHistory imageObj ∧ UnaryHistory coimageObj ∧
                  UnaryHistory comparison ∧ UnaryHistory recomposed := by
  intro fEmpty kerReadback cokReadback imageReadback coimageReadback comparisonReadback
    recomposedReadback
  have sameKerF : hsame kerObj f :=
    cont_left_unit_result kerReadback
  have kerEmpty : hsame kerObj BHist.Empty :=
    hsame_trans sameKerF fEmpty
  have sameCokF : hsame cokObj f :=
    cont_right_unit_result cokReadback
  have cokEmpty : hsame cokObj BHist.Empty :=
    hsame_trans sameCokF fEmpty
  have imageEmpty : hsame imageObj BHist.Empty :=
    cont_respects_hsame kerEmpty cokEmpty imageReadback (cont_left_unit BHist.Empty)
  have sameCoimageImage : hsame coimageObj imageObj :=
    cont_right_unit_result coimageReadback
  have coimageEmpty : hsame coimageObj BHist.Empty :=
    hsame_trans sameCoimageImage imageEmpty
  have sameComparisonCoimage : hsame comparison coimageObj :=
    cont_right_unit_result comparisonReadback
  have comparisonEmpty : hsame comparison BHist.Empty :=
    hsame_trans sameComparisonCoimage coimageEmpty
  have sameRecomposedComparison : hsame recomposed comparison :=
    cont_right_unit_result recomposedReadback
  have recomposedEmpty : hsame recomposed BHist.Empty :=
    hsame_trans sameRecomposedComparison comparisonEmpty
  have recomposedF : hsame recomposed f :=
    hsame_trans recomposedEmpty (hsame_symm fEmpty)
  have kerUnary : UnaryHistory kerObj :=
    unary_transport unary_empty (hsame_symm kerEmpty)
  have cokUnary : UnaryHistory cokObj :=
    unary_transport unary_empty (hsame_symm cokEmpty)
  have imageUnary : UnaryHistory imageObj :=
    unary_transport unary_empty (hsame_symm imageEmpty)
  have coimageUnary : UnaryHistory coimageObj :=
    unary_transport unary_empty (hsame_symm coimageEmpty)
  have comparisonUnary : UnaryHistory comparison :=
    unary_transport unary_empty (hsame_symm comparisonEmpty)
  have recomposedUnary : UnaryHistory recomposed :=
    unary_transport unary_empty (hsame_symm recomposedEmpty)
  exact And.intro kerEmpty
    (And.intro cokEmpty
      (And.intro imageEmpty
        (And.intro coimageEmpty
          (And.intro comparisonEmpty
            (And.intro recomposedF
              (And.intro kerUnary
                (And.intro cokUnary
                  (And.intro imageUnary
                  (And.intro coimageUnary
                      (And.intro comparisonUnary recomposedUnary))))))))))

theorem AbelianCatKernelCokernelCarrier_classifier_transport
    {obj hom zero biprod add kernel cokernel factor obj' hom' zero' biprod' add' kernel'
      cokernel' factor' : BHist} :
    AbelianCatKernelCokernelCarrier obj hom zero biprod add kernel cokernel factor ->
      hsame obj obj' -> hsame hom hom' -> hsame zero zero' -> hsame biprod biprod' ->
        hsame add add' -> hsame kernel kernel' -> hsame cokernel cokernel' ->
          hsame factor factor' ->
            AbelianCatKernelCokernelCarrier obj' hom' zero' biprod' add' kernel' cokernel'
                factor' ∧
              CategoryHomCarrier obj' obj' hom' ∧ Cont kernel' cokernel' factor' := by
  intro carrier sameObj sameHom sameZero sameBiprod sameAdd sameKernel sameCokernel sameFactor
  cases sameObj
  cases sameHom
  cases sameZero
  cases sameBiprod
  cases sameAdd
  cases sameKernel
  cases sameCokernel
  cases sameFactor
  exact And.intro carrier
    (And.intro carrier.right.right.left carrier.right.right.right.right.right.right.right.right)

theorem AbelianCatKernelCokernel_recomposition_audit_row
    {f kerObj cokObj imageObj coimageObj comparison recomposed audit : BHist} :
    hsame f BHist.Empty -> Cont BHist.Empty f kerObj -> Cont f BHist.Empty cokObj ->
      Cont kerObj cokObj imageObj -> Cont imageObj BHist.Empty coimageObj ->
        Cont coimageObj BHist.Empty comparison -> Cont comparison BHist.Empty recomposed ->
          Cont recomposed BHist.Empty audit ->
            hsame audit BHist.Empty ∧ hsame audit f ∧ UnaryHistory audit ∧
              UnaryHistory recomposed ∧ hsame recomposed f := by
  intro fEmpty kerReadback cokReadback imageReadback coimageReadback comparisonReadback
    recomposedReadback auditReadback
  have visibleRows :=
    AbelianCatKernelCokernel_visible_factorization fEmpty kerReadback cokReadback imageReadback
      coimageReadback comparisonReadback recomposedReadback
  have recomposedF : hsame recomposed f :=
    visibleRows.right.right.right.right.right.left
  have recomposedUnary : UnaryHistory recomposed :=
    visibleRows.right.right.right.right.right.right.right.right.right.right.right
  have sameAuditRecomposed : hsame audit recomposed :=
    cont_right_unit_result auditReadback
  have auditF : hsame audit f :=
    hsame_trans sameAuditRecomposed recomposedF
  have auditEmpty : hsame audit BHist.Empty :=
    hsame_trans auditF fEmpty
  have auditUnary : UnaryHistory audit :=
    unary_transport unary_empty (hsame_symm auditEmpty)
  exact And.intro auditEmpty
    (And.intro auditF (And.intro auditUnary (And.intro recomposedUnary recomposedF)))

structure AbelianCatZeroBiproductKernelSurface where
  source : BHist
  target : BHist
  zero : BHist
  add : BHist
  kernel : BHist
  cokernel : BHist
  factor : BHist
  carrier : AbelianCatAdditiveCarrier source target zero add kernel cokernel factor
  zero_hom : CategoryHomCarrier source target zero
  add_carrier : GroupSingletonCarrier add
  kernel_row : Cont zero add kernel
  factor_row : Cont kernel cokernel factor

theorem AbelianCatZeroBiproductKernelSurface_rows
    (S : AbelianCatZeroBiproductKernelSurface) :
    CategoryHomCarrier S.source S.target S.zero ∧ GroupSingletonCarrier S.add ∧
      Cont S.zero S.add S.kernel ∧ Cont S.kernel S.cokernel S.factor := by
  exact And.intro S.zero_hom
    (And.intro S.add_carrier (And.intro S.kernel_row S.factor_row))

theorem AbelianCatZeroBiproductKernelSurface_zero_object_transport
    (S : AbelianCatZeroBiproductKernelSurface) {zero' : BHist} :
    hsame S.zero zero' ->
      CategoryHomCarrier S.source S.target zero' ∧ Cont zero' S.add S.kernel := by
  intro sameZero
  have zeroHom : CategoryHomCarrier S.source S.target zero' :=
    CategoryHomCarrier_hsame_transport (hsame_refl S.source) (hsame_refl S.target) sameZero
      S.zero_hom
  have kernelRow : Cont zero' S.add S.kernel :=
    cont_hsame_transport sameZero (hsame_refl S.add) (hsame_refl S.kernel) S.kernel_row
  exact And.intro zeroHom kernelRow

theorem AbelianCatZeroBiproductKernelSurface_zero_object_boundary
    (S : AbelianCatZeroBiproductKernelSurface) :
    CategoryHomCarrier S.source S.target S.zero ∧ UnaryHistory S.zero ∧
      GroupSingletonCarrier S.add ∧ UnaryHistory S.add ∧ Cont S.zero S.add S.kernel := by
  have zeroUnary : UnaryHistory S.zero := S.zero_hom.right.right.left
  have addUnary : UnaryHistory S.add :=
    unary_transport unary_empty (hsame_symm S.add_carrier)
  exact And.intro S.zero_hom
    (And.intro zeroUnary (And.intro S.add_carrier (And.intro addUnary S.kernel_row)))

theorem AbelianCatZeroBiproductKernelSurface_additive_hom_boundary
    (S : AbelianCatZeroBiproductKernelSurface) {zeroAdd addFactor : BHist} :
    Cont S.zero S.add zeroAdd ->
      Cont zeroAdd S.cokernel addFactor ->
        CategoryHomCarrier S.source S.target S.zero ∧ GroupSingletonCarrier S.add ∧
          UnaryHistory S.zero ∧ UnaryHistory S.add ∧ UnaryHistory zeroAdd ∧
            Cont S.zero S.add zeroAdd ∧ hsame zeroAdd S.kernel ∧
              Cont zeroAdd S.cokernel S.factor ∧ hsame addFactor S.factor := by
  intro zeroAddRow addFactorRow
  have boundary := AbelianCatZeroBiproductKernelSurface_zero_object_boundary S
  have zeroUnary : UnaryHistory S.zero := boundary.right.left
  have addUnary : UnaryHistory S.add := boundary.right.right.right.left
  have zeroAddUnary : UnaryHistory zeroAdd :=
    unary_cont_closed zeroUnary addUnary zeroAddRow
  have zeroAddKernel : hsame zeroAdd S.kernel :=
    cont_deterministic zeroAddRow S.kernel_row
  have transportedFactor : Cont zeroAdd S.cokernel S.factor := by
    cases zeroAddKernel
    exact S.factor_row
  have addFactorSame : hsame addFactor S.factor :=
    cont_deterministic addFactorRow transportedFactor
  exact And.intro S.zero_hom
    (And.intro S.add_carrier
      (And.intro zeroUnary
        (And.intro addUnary
          (And.intro zeroAddUnary
            (And.intro zeroAddRow
              (And.intro zeroAddKernel
                (And.intro transportedFactor addFactorSame)))))))

theorem AbelianCatZeroBiproductKernelSurface_semantic_name_certificate :
    SemanticNameCert
      (fun h : BHist =>
        exists S : AbelianCatZeroBiproductKernelSurface, hsame h S.zero)
      (fun h : BHist =>
        exists S : AbelianCatZeroBiproductKernelSurface, hsame h S.kernel ∧
          Cont S.zero S.add S.kernel)
      (fun h : BHist =>
        exists S : AbelianCatZeroBiproductKernelSurface, hsame h S.zero ∧
          Cont S.kernel S.cokernel S.factor)
      (fun h k : BHist => hsame h k) := by
  have zeroHom : CategoryHomCarrier BHist.Empty BHist.Empty BHist.Empty :=
    CategoryHomCarrier_empty_identity unary_empty
  have emptyMetricCarrier : GroupSingletonCarrier BHist.Empty :=
    hsame_refl BHist.Empty
  have emptyKernelRow : Cont BHist.Empty BHist.Empty BHist.Empty :=
    cont_left_unit BHist.Empty
  have emptyFactorRow : Cont BHist.Empty BHist.Empty BHist.Empty :=
    cont_left_unit BHist.Empty
  let S : AbelianCatZeroBiproductKernelSurface := {
    source := BHist.Empty
    target := BHist.Empty
    zero := BHist.Empty
    add := BHist.Empty
    kernel := BHist.Empty
    cokernel := BHist.Empty
    factor := BHist.Empty
    carrier := And.intro zeroHom
      (And.intro emptyMetricCarrier
        (And.intro unary_empty
          (And.intro unary_empty
            (And.intro unary_empty (And.intro emptyKernelRow emptyFactorRow)))))
    zero_hom := zeroHom
    add_carrier := emptyMetricCarrier
    kernel_row := emptyKernelRow
    factor_row := emptyFactorRow
  }
  exact {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty
        (Exists.intro S (hsame_refl BHist.Empty))
      equiv_refl := by
        intro h _source
        exact hsame_refl h
      equiv_symm := by
        intro h k sameHK
        exact hsame_symm sameHK
      equiv_trans := by
        intro h k r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro h k sameHK sourceH
        cases sourceH with
        | intro T sameHZero =>
            exact Exists.intro T (hsame_trans (hsame_symm sameHK) sameHZero)
    }
    pattern_sound := by
      intro h sourceH
      cases sourceH with
      | intro T sameHZero =>
          have kernelZero : hsame T.kernel T.zero :=
            cont_respects_hsame (hsame_refl T.zero) T.add_carrier T.kernel_row
              (cont_right_unit T.zero)
          exact Exists.intro T
            (And.intro (hsame_trans sameHZero (hsame_symm kernelZero)) T.kernel_row)
    ledger_sound := by
      intro h sourceH
      cases sourceH with
      | intro T sameHZero =>
          exact Exists.intro T (And.intro sameHZero T.factor_row)
  }

theorem AbelianCatZeroBiproductKernelSurface_factor_tail_transport
    (S : AbelianCatZeroBiproductKernelSurface) {zeroAdd addFactor factorTail : BHist} :
    Cont S.zero S.add zeroAdd ->
      Cont zeroAdd S.cokernel addFactor ->
        Cont addFactor BHist.Empty factorTail ->
          hsame factorTail S.factor ∧ UnaryHistory factorTail ∧
            Cont zeroAdd S.cokernel S.factor ∧ hsame zeroAdd S.kernel := by
  intro zeroAddRow addFactorRow factorTailRow
  have boundary :
      CategoryHomCarrier S.source S.target S.zero ∧ GroupSingletonCarrier S.add ∧
        UnaryHistory S.zero ∧ UnaryHistory S.add ∧ UnaryHistory zeroAdd ∧
          Cont S.zero S.add zeroAdd ∧ hsame zeroAdd S.kernel ∧
            Cont zeroAdd S.cokernel S.factor ∧ hsame addFactor S.factor :=
    AbelianCatZeroBiproductKernelSurface_additive_hom_boundary S zeroAddRow addFactorRow
  have tailAddFactor : hsame factorTail addFactor :=
    cont_right_unit_result factorTailRow
  have tailFactor : hsame factorTail S.factor :=
    hsame_trans tailAddFactor boundary.right.right.right.right.right.right.right.right
  have factorUnary : UnaryHistory S.factor :=
    S.carrier.right.right.right.right.left
  have tailUnary : UnaryHistory factorTail :=
    unary_transport factorUnary (hsame_symm tailFactor)
  exact And.intro tailFactor
    (And.intro tailUnary
      (And.intro boundary.right.right.right.right.right.right.right.left
        boundary.right.right.right.right.right.right.left))

end BEDC.Derived.AbelianCatUp
