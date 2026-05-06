import BEDC.Derived.ProdUp

namespace BEDC.Derived.ProdUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

def ProdPairRep (Left Right : BHist → Prop) (h l r : BHist) : Prop :=
  Left l ∧ Right r ∧ Cont l r h

def ProdPairRepCoherent (Left Right : BHist → Prop)
    (LeftEq RightEq : BHist → BHist → Prop) : Prop :=
  ∀ {h l r l' r' : BHist},
    ProdPairRep Left Right h l r →
      ProdPairRep Left Right h l' r' →
        LeftEq l l' ∧ RightEq r r'

theorem ProdHistoryCarrier_empty_result_components {Left Right : BHist -> Prop} :
    ProdHistoryCarrier Left Right BHist.Empty ->
      exists l : BHist, exists r : BHist,
        Left l /\ Right r /\ hsame l BHist.Empty /\ hsame r BHist.Empty := by
  intro carrier
  cases carrier with
  | intro l rest =>
      cases rest with
      | intro r data =>
          cases data with
          | intro leftCarrier rightData =>
              cases rightData with
              | intro rightCarrier contEmpty =>
                  have emptyComponents := cont_empty_result_inversion contEmpty
                  exact Exists.intro l
                    (Exists.intro r
                      (And.intro leftCarrier
                        (And.intro rightCarrier
                          (And.intro emptyComponents.left emptyComponents.right))))

theorem ProdPairRep_coverage {Left Right : BHist -> Prop} {h : BHist} :
    ProdHistoryCarrier Left Right h <->
      exists l : BHist, exists r : BHist, ProdPairRep Left Right h l r := by
  constructor
  · intro carrier
    cases carrier with
    | intro l rest =>
        cases rest with
        | intro r data =>
            exact Exists.intro l (Exists.intro r data)
  · intro displayed
    cases displayed with
    | intro l rest =>
        cases rest with
        | intro r rep =>
            exact Exists.intro l (Exists.intro r rep)

theorem ProdHistoryClassifier_fixed_pair_determinism
    {Left Right : BHist → Prop} {h k l r : BHist} :
    Left l → Right r → Cont l r h → Cont l r k →
      hsame h k ∧ ProdHistoryClassifier Left Right h k := by
  intro leftCarrier rightCarrier contH contK
  have sameHK : hsame h k := cont_deterministic contH contK
  constructor
  · exact sameHK
  · exact And.intro
      (ProdHistoryCarrier_cont_intro leftCarrier rightCarrier contH)
      (And.intro
        (ProdHistoryCarrier_cont_intro leftCarrier rightCarrier contK)
        sameHK)

theorem ProdPairRep_hsame_transport {Left Right : BHist → Prop} {h k l r : BHist} :
    ProdPairRep Left Right h l r → hsame h k → ProdPairRep Left Right k l r := by
  intro rep sameHK
  cases rep with
  | intro leftCarrier rest =>
      cases rest with
      | intro rightCarrier contH =>
          exact And.intro leftCarrier
            (And.intro rightCarrier (cont_result_hsame_transport contH sameHK))

theorem ProdPairRep_fixed_endpoint_exactness {Left Right : BHist → Prop} {h k l r : BHist} :
    ProdPairRep Left Right h l r → (ProdPairRep Left Right k l r ↔ hsame h k) := by
  intro repH
  constructor
  · intro repK
    cases repH with
    | intro leftCarrier restH =>
        cases restH with
        | intro rightCarrier contH =>
            cases repK with
            | intro _leftCarrierK restK =>
                cases restK with
                | intro _rightCarrierK contK =>
                    exact
                      (ProdHistoryClassifier_fixed_pair_determinism
                        leftCarrier rightCarrier contH contK).left
  · intro sameHK
    exact ProdPairRep_hsame_transport repH sameHK

theorem ProdPairRep_singleton_endpoint_exactness_iff {l0 r0 h : BHist} :
    (exists l : BHist, exists r : BHist,
      ProdPairRep (fun x : BHist => hsame x l0) (fun y : BHist => hsame y r0) h l r) <->
      hsame h (append l0 r0) := by
  constructor
  · intro displayed
    cases displayed with
    | intro l rest =>
        cases rest with
        | intro r rep =>
            cases rep with
            | intro sameL rest =>
                cases rest with
                | intro sameR contH =>
                    cases sameL
                    cases sameR
                    exact contH
  · intro sameH
    exact Exists.intro l0
      (Exists.intro r0
        (And.intro (hsame_refl l0)
          (And.intro (hsame_refl r0) sameH)))

theorem ProdPairRep_hsame_coherence {Left Right : BHist → Prop}
    {LeftEq RightEq : BHist → BHist → Prop} {h k l r l' r' : BHist} :
    ProdPairRepCoherent Left Right LeftEq RightEq →
      ProdPairRep Left Right h l r →
        ProdPairRep Left Right k l' r' →
          hsame h k → LeftEq l l' ∧ RightEq r r' := by
  intro coherent repH repK sameHK
  have repKAtH : ProdPairRep Left Right h l' r' :=
    ProdPairRep_hsame_transport repK (hsame_symm sameHK)
  exact coherent repH repKAtH

theorem ProdCarrier_single_valued_displayed_pair_readback
    {Left Right : BHist -> Prop} {LeftEq RightEq : BHist -> BHist -> Prop} {h : BHist}
    (coherent : ProdPairRepCoherent Left Right LeftEq RightEq) :
    ProdHistoryCarrier Left Right h ->
      exists l : BHist, exists r : BHist,
        (Left l ∧ Right r ∧ Cont l r h) ∧
        (exists l0 : BHist, exists r0 : BHist, Left l0 ∧ Right r0 ∧ Cont l0 r0 h) ∧
        (forall {l' r' : BHist},
          Left l' -> Right r' -> Cont l' r' h -> LeftEq l l' ∧ RightEq r r') := by
  intro carrier
  cases carrier with
  | intro l rest =>
      cases rest with
      | intro r displayed =>
          exact Exists.intro l
            (Exists.intro r
              (And.intro displayed
                (And.intro
                  (Exists.intro l (Exists.intro r displayed))
                  (by
                    intro l' r' leftCarrier rightCarrier contH
                    exact coherent displayed
                      (And.intro leftCarrier (And.intro rightCarrier contH))))))

theorem ProdPairRep_e0_unit_coherence_absurd {Left Right : BHist -> Prop}
    (leftEmpty : Left BHist.Empty) (leftZero : Left (BHist.e0 BHist.Empty))
    (rightEmpty : Right BHist.Empty) (rightZero : Right (BHist.e0 BHist.Empty))
    (coherent : ProdPairRepCoherent Left Right hsame hsame) : False := by
  have leftUnitRep :
      ProdPairRep Left Right (BHist.e0 BHist.Empty) BHist.Empty
        (BHist.e0 BHist.Empty) :=
    And.intro leftEmpty
      (And.intro rightZero (cont_left_unit (BHist.e0 BHist.Empty)))
  have rightUnitRep :
      ProdPairRep Left Right (BHist.e0 BHist.Empty) (BHist.e0 BHist.Empty)
        BHist.Empty :=
    And.intro leftZero
      (And.intro rightEmpty (cont_right_unit (BHist.e0 BHist.Empty)))
  have forcedSame := coherent leftUnitRep rightUnitRep
  exact not_hsame_emp_e0 forcedSame.left

theorem ProdPairRep_classifier_bounded_coherence {Left Right : BHist -> Prop}
    {LeftEq RightEq : BHist -> BHist -> Prop}
    (leftCert : BEDC.FKernel.NameCert.NameCert Left LeftEq)
    (rightCert : BEDC.FKernel.NameCert.NameCert Right RightEq)
    {leftCenter rightCenter : BHist}
    (leftBound : forall {l : BHist}, Left l -> LeftEq l leftCenter)
    (rightBound : forall {r : BHist}, Right r -> RightEq r rightCenter) :
    ProdPairRepCoherent Left Right LeftEq RightEq := by
  intro h l r l' r' rep rep'
  cases rep with
  | intro leftL rest =>
      cases rest with
      | intro rightR _cont =>
          cases rep' with
          | intro leftL' rest' =>
              cases rest' with
              | intro rightR' _cont' =>
                  constructor
                  · exact leftCert.equiv_trans (leftBound leftL)
                      (leftCert.equiv_symm (leftBound leftL'))
                  · exact rightCert.equiv_trans (rightBound rightR)
                      (rightCert.equiv_symm (rightBound rightR'))

theorem ProdHistoryClassifier_cont_congr {Left Right : BHist → Prop}
    (left_transport : ∀ {x y : BHist}, hsame x y → Left x → Left y)
    (right_transport : ∀ {x y : BHist}, hsame x y → Right x → Right y)
    {l l' r r' h h' : BHist} :
    Left l → Right r → hsame l l' → hsame r r' → Cont l r h → Cont l' r' h' →
      ProdHistoryClassifier Left Right h h' := by
  intro leftCarrier rightCarrier sameLeft sameRight contH contH'
  have leftCarrier' : Left l' := left_transport sameLeft leftCarrier
  have rightCarrier' : Right r' := right_transport sameRight rightCarrier
  have sameEndpoints : hsame h h' :=
    cont_respects_hsame sameLeft sameRight contH contH'
  exact And.intro
    (ProdHistoryCarrier_cont_intro leftCarrier rightCarrier contH)
    (And.intro
      (ProdHistoryCarrier_cont_intro leftCarrier' rightCarrier' contH')
      sameEndpoints)

theorem ProdHistoryCarrier_displayed_pair_semantic_name_certificate
    (Left Right : BHist → Prop)
    (left_witness : ∃ l : BHist, Left l) (right_witness : ∃ r : BHist, Right r) :
    SemanticNameCert (ProdHistoryCarrier Left Right) (ProdHistoryCarrier Left Right)
      (fun h : BHist => ∃ l : BHist, ∃ r : BHist, ProdPairRep Left Right h l r)
      (ProdHistoryClassifier Left Right) := by
  have base := prod_history_semantic_name_certificate Left Right left_witness right_witness
  exact {
    core := base.core
    pattern_sound := base.pattern_sound
    ledger_sound := by
      intro h carrier
      exact ProdPairRep_coverage.mp carrier
  }

end BEDC.Derived.ProdUp
