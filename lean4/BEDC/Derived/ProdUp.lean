import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ProdUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def ProdHistoryCarrier (Left Right : BHist -> Prop) (h : BHist) : Prop :=
  exists l : BHist, exists r : BHist, Left l ∧ Right r ∧ Cont l r h

def ProdHistoryClassifier (Left Right : BHist -> Prop) (h k : BHist) : Prop :=
  ProdHistoryCarrier Left Right h ∧ ProdHistoryCarrier Left Right k ∧ hsame h k

def ProdComponentHistoryClassifier (Left Right : BHist -> Prop)
    (LeftEq RightEq : BHist -> BHist -> Prop) (h k : BHist) : Prop :=
  exists lh rh lk rk : BHist,
    Left lh /\ Right rh /\ Cont lh rh h /\
      Left lk /\ Right rk /\ Cont lk rk k /\ LeftEq lh lk /\ RightEq rh rk

theorem ProdHistoryClassifier_component_inversion {Left Right : BHist → Prop} {h k : BHist} :
    ProdHistoryClassifier Left Right h k ↔
      ∃ l r l' r' : BHist,
        Left l ∧ Right r ∧ Cont l r h ∧
          Left l' ∧ Right r' ∧ Cont l' r' k ∧ hsame h k := by
  constructor
  · intro classifier
    cases classifier with
    | intro carrierH rest =>
        cases rest with
        | intro carrierK sameHK =>
            cases carrierH with
            | intro l leftRest =>
                cases leftRest with
                | intro r leftData =>
                    cases leftData with
                    | intro leftCarrier rightData =>
                        cases rightData with
                        | intro rightCarrier contH =>
                            cases carrierK with
                            | intro l' rightRest =>
                                cases rightRest with
                                | intro r' rightData' =>
                                    cases rightData' with
                                    | intro leftCarrier' tailData =>
                                        cases tailData with
                                        | intro rightCarrier' contK =>
                                            exact Exists.intro l
                                              (Exists.intro r
                                                (Exists.intro l'
                                                  (Exists.intro r'
                                                    (And.intro leftCarrier
                                                      (And.intro rightCarrier
                                                        (And.intro contH
                                                          (And.intro leftCarrier'
                                                            (And.intro rightCarrier'
                                                              (And.intro contK sameHK)))))))))
  · intro witness
    cases witness with
    | intro l rest =>
        cases rest with
        | intro r rest =>
            cases rest with
            | intro l' rest =>
                cases rest with
                | intro r' data =>
                    cases data with
                    | intro leftCarrier rest =>
                        cases rest with
                        | intro rightCarrier rest =>
                            cases rest with
                            | intro contH rest =>
                                cases rest with
                                | intro leftCarrier' rest =>
                                    cases rest with
                                    | intro rightCarrier' rest =>
                                        cases rest with
                                        | intro contK sameHK =>
                                            exact And.intro
                                              (Exists.intro l
                                                (Exists.intro r
                                                  (And.intro leftCarrier
                                                    (And.intro rightCarrier contH))))
                                              (And.intro
                                                (Exists.intro l'
                                                (Exists.intro r'
                                                  (And.intro leftCarrier'
                                                    (And.intro rightCarrier' contK))))
                                                sameHK)

theorem ProdHistoryClassifier_common_right_component_left_hsame
    {Left Right : BHist -> Prop} {h k l l' r : BHist} :
    ProdHistoryClassifier Left Right h k -> Cont l r h -> Cont l' r k -> hsame l l' := by
  intro classifier contLeft contRight
  exact cont_common_suffix_cancellation contLeft contRight classifier.right.right

theorem ProdHistoryCarrier_append_intro {Left Right : BHist -> Prop} {l r : BHist} :
    Left l -> Right r -> ProdHistoryCarrier Left Right (append l r) := by
  intro leftCarrier rightCarrier
  exact Exists.intro l
    (Exists.intro r
      (And.intro leftCarrier
        (And.intro rightCarrier (cont_intro (h := l) (k := r) rfl))))

theorem ProdHistoryCarrier_cont_intro {Left Right : BHist -> Prop} {l r h : BHist} :
    Left l -> Right r -> Cont l r h -> ProdHistoryCarrier Left Right h := by
  intro leftCarrier rightCarrier hCont
  exact Exists.intro l
    (Exists.intro r
      (And.intro leftCarrier
        (And.intro rightCarrier hCont)))

theorem ProdHistoryCarrier_visible_result_cases {Left Right : BHist -> Prop} {tail : BHist} :
    (ProdHistoryCarrier Left Right (BHist.e0 tail) ->
      exists l : BHist, exists r : BHist,
        Left l /\ Right r /\
          ((r = BHist.Empty /\ hsame l (BHist.e0 tail)) \/
            exists r0 : BHist, r = BHist.e0 r0 /\ Cont l r0 tail)) /\
      (ProdHistoryCarrier Left Right (BHist.e1 tail) ->
        exists l : BHist, exists r : BHist,
          Left l /\ Right r /\
            ((r = BHist.Empty /\ hsame l (BHist.e1 tail)) \/
              exists r0 : BHist, r = BHist.e1 r0 /\ Cont l r0 tail)) := by
  constructor
  · intro carrier
    cases carrier with
    | intro l rest =>
        cases rest with
        | intro r data =>
            exact ⟨l, r, data.left, data.right.left, cont_e0_result_inversion data.right.right⟩
  · intro carrier
    cases carrier with
    | intro l rest =>
        cases rest with
        | intro r data =>
            exact ⟨l, r, data.left, data.right.left, cont_e1_result_inversion data.right.right⟩

theorem ProdComponentHistoryClassifier_endpoint_carriers {Left Right : BHist -> Prop}
    {LeftEq RightEq : BHist -> BHist -> Prop} {h k : BHist} :
    ProdComponentHistoryClassifier Left Right LeftEq RightEq h k ->
      ProdHistoryCarrier Left Right h /\ ProdHistoryCarrier Left Right k := by
  intro classifier
  cases classifier with
  | intro lh rest =>
      cases rest with
      | intro rh rest =>
          cases rest with
          | intro lk rest =>
              cases rest with
              | intro rk data =>
                  cases data with
                  | intro leftH rest =>
                      cases rest with
                      | intro rightH rest =>
                          cases rest with
                          | intro contH rest =>
                              cases rest with
                              | intro leftK rest =>
                                  cases rest with
                                  | intro rightK rest =>
                                      cases rest with
                                      | intro contK _componentSame =>
                                          constructor
                                          · exact
                                              ProdHistoryCarrier_cont_intro
                                                leftH rightH contH
                                          · exact
                                              ProdHistoryCarrier_cont_intro
                                                leftK rightK contK

theorem ProdComponentHistoryClassifier_hsame_transport {Left Right : BHist -> Prop}
    {LeftEq RightEq : BHist -> BHist -> Prop} {h h' k k' : BHist} :
    hsame h h' -> hsame k k' ->
      ProdComponentHistoryClassifier Left Right LeftEq RightEq h k ->
        ProdComponentHistoryClassifier Left Right LeftEq RightEq h' k' := by
  intro sameH sameK classifier
  cases classifier with
  | intro lh restLH =>
      cases restLH with
      | intro rh restRH =>
          cases restRH with
          | intro lk restLK =>
              cases restLK with
              | intro rk data =>
                  cases data with
                  | intro leftH rest =>
                      cases rest with
                      | intro rightH rest =>
                          cases rest with
                          | intro contH rest =>
                              cases rest with
                              | intro leftK rest =>
                                  cases rest with
                                  | intro rightK rest =>
                                      cases rest with
                                      | intro contK componentSame =>
                                          exact Exists.intro lh
                                            (Exists.intro rh
                                              (Exists.intro lk
                                                (Exists.intro rk
                                                  (And.intro leftH
                                                    (And.intro rightH
                                                      (And.intro
                                                        (cont_result_hsame_transport contH sameH)
                                                        (And.intro leftK
                                                          (And.intro rightK
                                                            (And.intro
                                                              (cont_result_hsame_transport
                                                                contK sameK)
                                                              componentSame)))))))))

theorem ProdHistoryCarrier_unary_of_components {Left Right : BHist -> Prop}
    (left_unary : forall {l : BHist}, Left l -> BEDC.FKernel.Unary.UnaryHistory l)
    (right_unary : forall {r : BHist}, Right r -> BEDC.FKernel.Unary.UnaryHistory r)
    {h : BHist} :
    ProdHistoryCarrier Left Right h -> BEDC.FKernel.Unary.UnaryHistory h := by
  intro carrier
  cases carrier with
  | intro l rest =>
      cases rest with
      | intro r data =>
          cases data with
          | intro leftCarrier rightData =>
              cases rightData with
              | intro rightCarrier cont =>
                  exact unary_cont_closed (left_unary leftCarrier) (right_unary rightCarrier) cont

theorem ProdHistoryCarrier_unary {h : BHist} :
    ProdHistoryCarrier UnaryHistory UnaryHistory h -> UnaryHistory h := by
  intro carrier
  cases carrier with
  | intro leftHist rest =>
      cases rest with
      | intro rightHist data =>
          cases data with
          | intro leftUnary rightData =>
              cases rightData with
              | intro rightUnary cont =>
                  exact unary_cont_closed leftUnary rightUnary cont

theorem ProdHistoryCarrier_hsame_transport {Left Right : BHist -> Prop} {h k : BHist} :
    hsame h k -> ProdHistoryCarrier Left Right h -> ProdHistoryCarrier Left Right k := by
  intro same carrier
  cases carrier with
  | intro leftHist rest =>
      cases rest with
      | intro rightHist data =>
          cases data with
          | intro leftCarrier rightData =>
              cases rightData with
              | intro rightCarrier cont =>
                  exact Exists.intro leftHist
                    (Exists.intro rightHist
                      (And.intro leftCarrier
                        (And.intro rightCarrier (cont_result_hsame_transport cont same))))

def ProdHistoryLedgerPolicy (Left Right : BHist -> Prop) (raw visible : BHist) : Prop :=
  ProdHistoryCarrier Left Right raw ∧ hsame raw visible

theorem ProdHistoryLedgerPolicy_visible_carrier {Left Right : BHist -> Prop}
    {raw visible : BHist} :
    ProdHistoryLedgerPolicy Left Right raw visible -> ProdHistoryCarrier Left Right visible := by
  intro ledger
  cases ledger with
  | intro rawCarrier sameRawVisible =>
      exact ProdHistoryCarrier_hsame_transport sameRawVisible rawCarrier

theorem ProdHistoryLedgerPolicy_raw_visible_classifier {Left Right : BHist -> Prop}
    {raw visible : BHist} :
    ProdHistoryLedgerPolicy Left Right raw visible -> ProdHistoryClassifier Left Right raw visible := by
  intro ledger
  cases ledger with
  | intro rawCarrier sameRawVisible =>
      exact And.intro rawCarrier
        (And.intro (ProdHistoryLedgerPolicy_visible_carrier
          (And.intro rawCarrier sameRawVisible)) sameRawVisible)

theorem ProdHistoryLedgerPolicy_hsame_transport {Left Right : BEDC.FKernel.Hist.BHist -> Prop}
    {raw raw' visible visible' : BEDC.FKernel.Hist.BHist} :
    BEDC.FKernel.Hist.hsame raw raw' -> BEDC.FKernel.Hist.hsame visible visible' ->
      ProdHistoryLedgerPolicy Left Right raw visible ->
        ProdHistoryLedgerPolicy Left Right raw' visible' := by
  intro sameRaw sameVisible ledger
  cases ledger with
  | intro rawCarrier sameRawVisible =>
      exact And.intro (ProdHistoryCarrier_hsame_transport sameRaw rawCarrier)
        (BEDC.FKernel.Hist.hsame_trans (BEDC.FKernel.Hist.hsame_symm sameRaw)
          (BEDC.FKernel.Hist.hsame_trans sameRawVisible sameVisible))

theorem ProdHistoryClassifier_right_hsame_transport {Left Right : BHist -> Prop}
    {h k k' : BHist} :
    ProdHistoryClassifier Left Right h k ->
      hsame k k' -> ProdHistoryClassifier Left Right h k' := by
  intro classified sameRight
  cases classified with
  | intro carrierH rest =>
      cases rest with
      | intro carrierK sameHK =>
          exact And.intro carrierH
            (And.intro (ProdHistoryCarrier_hsame_transport sameRight carrierK)
              (hsame_trans sameHK sameRight))

theorem ProdHistoryClassifier_hsame_transport {Left Right : BEDC.FKernel.Hist.BHist -> Prop}
    {h h' k k' : BEDC.FKernel.Hist.BHist} :
    BEDC.FKernel.Hist.hsame h h' -> BEDC.FKernel.Hist.hsame k k' ->
      ProdHistoryClassifier Left Right h k -> ProdHistoryClassifier Left Right h' k' := by
  intro sameLeft sameRight classified
  cases classified with
  | intro carrierH rest =>
      cases rest with
      | intro carrierK sameHK =>
          constructor
          · exact ProdHistoryCarrier_hsame_transport sameLeft carrierH
          · constructor
            · exact ProdHistoryCarrier_hsame_transport sameRight carrierK
            · exact BEDC.FKernel.Hist.hsame_trans
                (BEDC.FKernel.Hist.hsame_symm sameLeft)
                (BEDC.FKernel.Hist.hsame_trans sameHK sameRight)

theorem ProdHistoryClassifier_symm {Left Right : BHist -> Prop} {h k : BHist} :
    ProdHistoryClassifier Left Right h k -> ProdHistoryClassifier Left Right k h := by
  intro classified
  cases classified with
  | intro carrierH rest =>
      cases rest with
      | intro carrierK sameHK =>
          exact And.intro carrierK (And.intro carrierH (hsame_symm sameHK))

theorem ProdHistoryClassifier_left_hsame_transport {Left Right : BHist -> Prop}
    {h h' k : BHist} :
    ProdHistoryClassifier Left Right h k ->
      hsame h h' -> ProdHistoryClassifier Left Right h' k := by
  intro classified sameLeft
  cases classified with
  | intro carrierH rest =>
      cases rest with
      | intro carrierK sameHK =>
          exact And.intro (ProdHistoryCarrier_hsame_transport sameLeft carrierH)
            (And.intro carrierK (hsame_trans (hsame_symm sameLeft) sameHK))

theorem ProdHistoryClassifier_trans {Left Right : BHist -> Prop} {h k r : BHist} :
    ProdHistoryClassifier Left Right h k ->
      ProdHistoryClassifier Left Right k r -> ProdHistoryClassifier Left Right h r := by
  intro leftClass rightClass
  cases leftClass with
  | intro carrierH leftRest =>
      cases leftRest with
      | intro _ sameHK =>
          cases rightClass with
          | intro _ rightRest =>
              cases rightRest with
              | intro carrierR sameKR =>
                  exact And.intro carrierH
                    (And.intro carrierR (hsame_trans sameHK sameKR))

theorem ProdHistoryLedgerPolicy_classifier_extension {Left Right : BHist -> Prop}
    {raw visible target : BHist} :
    ProdHistoryLedgerPolicy Left Right raw visible ->
      ProdHistoryClassifier Left Right visible target ->
        ProdHistoryClassifier Left Right raw target := by
  intro ledger visibleTarget
  exact ProdHistoryClassifier_trans
    (ProdHistoryLedgerPolicy_raw_visible_classifier ledger)
    visibleTarget

theorem ProdHistoryLedgerPolicy_classifier_backward_composition
    {Left Right : BHist → Prop} {rho v w : BHist} :
    ProdHistoryLedgerPolicy Left Right rho v →
      ProdHistoryClassifier Left Right w v → ProdHistoryClassifier Left Right w rho := by
  intro ledger classifier
  exact ProdHistoryClassifier_trans classifier
    (ProdHistoryClassifier_symm (ProdHistoryLedgerPolicy_raw_visible_classifier ledger))

theorem ProdHistoryLedgerPolicy_two_step_classifier_composition
    {Left Right : BHist -> Prop} {rho v w : BHist} :
    ProdHistoryLedgerPolicy Left Right rho v ->
      ProdHistoryLedgerPolicy Left Right v w ->
        ProdHistoryClassifier Left Right rho w := by
  intro firstLedger secondLedger
  exact ProdHistoryClassifier_trans
    (ProdHistoryLedgerPolicy_raw_visible_classifier firstLedger)
    (ProdHistoryLedgerPolicy_raw_visible_classifier secondLedger)

theorem ProdHistoryLedgerPolicy_component_exposure {Left Right : BHist -> Prop}
    {rho v : BHist} :
    ProdHistoryLedgerPolicy Left Right rho v ->
      exists l : BHist, exists r : BHist,
        Left l ∧ Right r ∧ Cont l r rho ∧ hsame rho v ∧
          ProdHistoryCarrier Left Right v ∧ ProdHistoryClassifier Left Right rho v := by
  intro ledger
  cases ledger with
  | intro rawCarrier sameRawVisible =>
      cases rawCarrier with
      | intro l restL =>
          cases restL with
          | intro r componentData =>
              cases componentData with
              | intro leftCarrier rest =>
                  cases rest with
                  | intro rightCarrier contRho =>
                      have rawCarrierRho : ProdHistoryCarrier Left Right rho :=
                        Exists.intro l
                          (Exists.intro r
                            (And.intro leftCarrier (And.intro rightCarrier contRho)))
                      have ledgerRhoVisible : ProdHistoryLedgerPolicy Left Right rho v :=
                        And.intro rawCarrierRho sameRawVisible
                      exact Exists.intro l
                        (Exists.intro r
                          (And.intro leftCarrier
                            (And.intro rightCarrier
                              (And.intro contRho
                                (And.intro sameRawVisible
                                  (And.intro
                                    (ProdHistoryLedgerPolicy_visible_carrier ledgerRhoVisible)
                                    (ProdHistoryLedgerPolicy_raw_visible_classifier
                                      ledgerRhoVisible)))))))

theorem prod_history_semantic_name_certificate (Left Right : BHist -> Prop)
    (left_witness : exists l : BHist, Left l) (right_witness : exists r : BHist, Right r) :
    SemanticNameCert (ProdHistoryCarrier Left Right) (ProdHistoryCarrier Left Right)
      (ProdHistoryCarrier Left Right) (ProdHistoryClassifier Left Right) := by
  cases left_witness with
  | intro l leftCarrier =>
      cases right_witness with
      | intro r rightCarrier =>
          exact {
            core := {
              carrier_inhabited := Exists.intro (append l r)
                (Exists.intro l
                  (Exists.intro r
                    (And.intro leftCarrier
                      (And.intro rightCarrier (cont_intro (h := l) (k := r) rfl)))))
              equiv_refl := by
                intro h carrier
                exact And.intro carrier (And.intro carrier (hsame_refl h))
              equiv_symm := by
                intro h k same
                cases same with
                | intro carrierH rest =>
                    cases rest with
                    | intro carrierK sameHK =>
                        exact And.intro carrierK (And.intro carrierH (hsame_symm sameHK))
              equiv_trans := by
                intro h k s sameHK sameKS
                cases sameHK with
                | intro carrierH restHK =>
                    cases restHK with
                    | intro _ sameHistHK =>
                        cases sameKS with
                        | intro _ restKS =>
                            cases restKS with
                            | intro carrierS sameHistKS =>
                                exact And.intro carrierH
                                  (And.intro carrierS (hsame_trans sameHistHK sameHistKS))
              carrier_respects_equiv := by
                intro h k same _
                exact same.right.left
            }
            pattern_sound := by
              intro h carrier
              exact carrier
            ledger_sound := by
              intro h carrier
              exact carrier
          }

def ProdCarrier (A B : Type) := Prod A B

def ProdClassifierSpec {A B : Type} (sameA : A → A → Prop) (sameB : B → B → Prop)
    (x y : ProdCarrier A B) : Prop :=
  sameA x.1 y.1 ∧ sameB x.2 y.2

def ProdClassifier {α β : Type} (left : α → α → Prop) (right : β → β → Prop)
    (x y : α × β) : Prop :=
  left x.1 y.1 ∧ right x.2 y.2

theorem prodClassifier_iff {α β : Type} {leftSame : α → α → Prop}
    {rightSame : β → β → Prop} {x y : ProdCarrier α β} :
    ProdClassifier leftSame rightSame x y ↔ leftSame x.1 y.1 ∧ rightSame x.2 y.2 := by
  constructor <;> intro h <;> exact h

theorem prod_stability_certificate_fields {A B : Type} {sameA : A → A → Prop}
    {sameB : B → B → Prop} (reflA : ∀ a, sameA a a) (reflB : ∀ b, sameB b b)
    (transA : ∀ {a b c}, sameA a b → sameA b c → sameA a c)
    (transB : ∀ {a b c}, sameB a b → sameB b c → sameB a c) :
    (∀ x : ProdCarrier A B, ProdClassifierSpec sameA sameB x x) ∧
      (∀ {x y z : ProdCarrier A B},
        ProdClassifierSpec sameA sameB x y →
          ProdClassifierSpec sameA sameB y z →
            ProdClassifierSpec sameA sameB x z) ∧
      (∀ {x y : ProdCarrier A B},
        ProdClassifierSpec sameA sameB x y → sameA x.1 y.1 ∧ sameB x.2 y.2) := by
  constructor
  · intro x
    cases x with
    | mk a b =>
        constructor
        · exact reflA a
        · exact reflB b
  · constructor
    · intro x y z hxy hyz
      cases x with
      | mk xa xb =>
          cases y with
          | mk ya yb =>
              cases z with
              | mk za zb =>
                  cases hxy with
                  | intro hAxy hBxy =>
                      cases hyz with
                      | intro hAyz hByz =>
                          constructor
                          · exact transA hAxy hAyz
                          · exact transB hBxy hByz
    · intro x y hxy
      exact hxy

theorem prodClassifierSpec_trans {A B : Type} {sameA : A -> A -> Prop}
    {sameB : B -> B -> Prop}
    (transA : forall {a b c : A}, sameA a b -> sameA b c -> sameA a c)
    (transB : forall {a b c : B}, sameB a b -> sameB b c -> sameB a c)
    {x y z : Prod A B} :
    ProdClassifierSpec sameA sameB x y ->
      ProdClassifierSpec sameA sameB y z -> ProdClassifierSpec sameA sameB x z := by
  intro hxy hyz
  cases x with
  | mk xa xb =>
      cases y with
      | mk ya yb =>
          cases z with
          | mk za zb =>
              cases hxy with
              | intro hAxy hBxy =>
                  cases hyz with
                  | intro hAyz hByz =>
                      exact ⟨transA hAxy hAyz, transB hBxy hByz⟩

theorem prod_stability_certificate {A B : Type} {sameA : A -> A -> Prop}
    {sameB : B -> B -> Prop} (reflA : forall a : A, sameA a a)
    (reflB : forall b : B, sameB b b)
    (transA : forall {a b c : A}, sameA a b -> sameA b c -> sameA a c)
    (transB : forall {a b c : B}, sameB a b -> sameB b c -> sameB a c) :
    (forall x : A × B, sameA x.1 x.1 /\ sameB x.2 x.2) /\
      (forall {x y z : A × B}, (sameA x.1 y.1 /\ sameB x.2 y.2) ->
        (sameA y.1 z.1 /\ sameB y.2 z.2) ->
          (sameA x.1 z.1 /\ sameB x.2 z.2)) /\
        (forall {x y : A × B}, (sameA x.1 y.1 /\ sameB x.2 y.2) ->
          sameA x.1 y.1) /\
          (forall {x y : A × B}, (sameA x.1 y.1 /\ sameB x.2 y.2) ->
            sameB x.2 y.2) := by
  constructor
  · intro x
    constructor
    · exact reflA x.1
    · exact reflB x.2
  · constructor
    · intro x y z hxy hyz
      constructor
      · exact transA hxy.left hyz.left
      · exact transB hxy.right hyz.right
    · constructor
      · intro x y hxy
        exact hxy.left
      · intro x y hxy
        exact hxy.right

theorem ProdClassifierSpec_trans {A B : Type} {relA : A → A → Prop} {relB : B → B → Prop}
    (transA : ∀ {a b c : A}, relA a b → relA b c → relA a c)
    (transB : ∀ {a b c : B}, relB a b → relB b c → relB a c)
    {x y z : ProdCarrier A B} :
    ProdClassifierSpec relA relB x y →
      ProdClassifierSpec relA relB y z →
        ProdClassifierSpec relA relB x z := by
  intro hxy hyz
  cases hxy with
  | intro leftXY rightXY =>
      cases hyz with
      | intro leftYZ rightYZ =>
          constructor
          · exact transA leftXY leftYZ
          · exact transB rightXY rightYZ

theorem ProdClassifierSpec_hsame_symm
    {x y : ProdCarrier BEDC.FKernel.Hist.BHist BEDC.FKernel.Hist.BHist} :
    ProdClassifierSpec BEDC.FKernel.Hist.hsame BEDC.FKernel.Hist.hsame x y →
      ProdClassifierSpec BEDC.FKernel.Hist.hsame BEDC.FKernel.Hist.hsame y x := by
  intro hxy
  cases hxy with
  | intro leftXY rightXY =>
      constructor
      · exact BEDC.FKernel.Hist.hsame_symm leftXY
      · exact BEDC.FKernel.Hist.hsame_symm rightXY

end BEDC.Derived.ProdUp
