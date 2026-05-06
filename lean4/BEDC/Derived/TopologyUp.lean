import BEDC.Derived.TopologyUp.Core
import BEDC.Derived.TopologyUp.FiniteBaseNeighborhood
import BEDC.Derived.TopologyUp.Singleton

namespace BEDC.Derived.TopologyUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def BHistIndexedNeighborhood (T : BHistIndexedOpenCarrier) (x : BHist) (i : T.OpenIx) :
    Prop :=
  UnaryHistory x ∧ T.OpenAt i x

def TopologyNeighborhood (T : BHistIndexedOpenCarrier) (x : BHist) (i : T.OpenIx) :
    Prop :=
  T.OpenAt i x

theorem TopologyNeighborhood_finite_intersection (T : BHistIndexedOpenCarrier)
    {i j : T.OpenIx} {x : BHist} :
    UnaryHistory x ->
      (TopologyNeighborhood T x (T.meet i j) <->
        (TopologyNeighborhood T x i ∧ TopologyNeighborhood T x j)) := by
  intro unaryX
  exact T.meet_law unaryX

theorem BHistUnaryTopologyLedgerRow_classifier_transport (T : BHistIndexedOpenCarrier)
    {i : T.OpenIx} {U : BHist -> Prop} :
    BHistUnaryTopologyLedgerRow T i U ->
      forall {x y : BHist}, UnaryHistory x -> UnaryHistory y -> hsame x y -> (U x <-> U y) := by
  intro row
  cases row with
  | singletonMetricBall ledger unaryLedger carries =>
      exact BHistCarriesOpen_classifier_transport T carries
  | finiteListIntersection ledger unaryLedger carries =>
      exact BHistCarriesOpen_classifier_transport T carries
  | binaryGeneratedMeet ledger unaryLedger carries =>
      exact BHistCarriesOpen_classifier_transport T carries
  | arbitraryUnion ledger unaryLedger carries =>
      exact BHistCarriesOpen_classifier_transport T carries
  | bottom ledger unaryLedger carries =>
      exact BHistCarriesOpen_classifier_transport T carries
  | top ledger unaryLedger carries =>
      exact BHistCarriesOpen_classifier_transport T carries

theorem BHistGeneratedOpenExact_row_coverage (T : BHistIndexedOpenCarrier)
    {U : BHist -> Prop} :
    BHistGeneratedOpenExact T U ->
      exists i : T.OpenIx, exists ledger : BHist,
        UnaryHistory ledger ∧ BHistUnaryTopologyLedgerRow T i U ∧
          BHistCarriesOpen T i U := by
  intro generated
  cases generated with
  | intro i carries =>
      exact Exists.intro i
        (Exists.intro BHist.Empty
          (And.intro unary_empty
            (And.intro
              (BHistUnaryTopologyLedgerRow.finiteListIntersection BHist.Empty unary_empty carries)
              carries)))

theorem BHistCarriesOpen_membership_transport_route (T : BHistIndexedOpenCarrier)
    {i : T.OpenIx} {U : BHist -> Prop} {x y : BHist} :
    BHistCarriesOpen T i U -> UnaryHistory x -> UnaryHistory y -> hsame x y -> U x ->
      T.OpenAt i x ∧ T.OpenAt i y ∧ U y := by
  intro carries unaryX unaryY sameXY ux
  have carryX : U x <-> T.OpenAt i x :=
    carries unaryX
  have carryY : U y <-> T.OpenAt i y :=
    carries unaryY
  have stable : T.OpenAt i x <-> T.OpenAt i y :=
    T.membership_stable unaryX unaryY sameXY
  have openX : T.OpenAt i x :=
    Iff.mp carryX ux
  have openY : T.OpenAt i y :=
    Iff.mp stable openX
  exact And.intro openX (And.intro openY (Iff.mpr carryY openY))

def BHistUnaryTopologyLedgerRow_constructorTag (T : BHistIndexedOpenCarrier)
    {i : T.OpenIx} {U : BHist -> Prop} (row : BHistUnaryTopologyLedgerRow T i U)
    (tag : BHist) : Prop :=
  (exists ledger : BHist, exists unaryLedger : UnaryHistory ledger,
    exists carries : BHistCarriesOpen T i U,
      row = BHistUnaryTopologyLedgerRow.singletonMetricBall ledger unaryLedger carries ∧
        hsame tag BHist.Empty) ∨
  (exists ledger : BHist, exists unaryLedger : UnaryHistory ledger,
    exists carries : BHistCarriesOpen T i U,
      row = BHistUnaryTopologyLedgerRow.finiteListIntersection ledger unaryLedger carries ∧
        hsame tag (BHist.e0 BHist.Empty)) ∨
  (exists ledger : BHist, exists unaryLedger : UnaryHistory ledger,
    exists carries : BHistCarriesOpen T i U,
      row = BHistUnaryTopologyLedgerRow.binaryGeneratedMeet ledger unaryLedger carries ∧
        hsame tag (BHist.e1 BHist.Empty)) ∨
  (exists ledger : BHist, exists unaryLedger : UnaryHistory ledger,
    exists carries : BHistCarriesOpen T i U,
      row = BHistUnaryTopologyLedgerRow.arbitraryUnion ledger unaryLedger carries ∧
        hsame tag (BHist.e0 (BHist.e0 BHist.Empty))) ∨
  (exists ledger : BHist, exists unaryLedger : UnaryHistory ledger,
    exists carries : BHistCarriesOpen T i U,
      row = BHistUnaryTopologyLedgerRow.bottom ledger unaryLedger carries ∧
        hsame tag (BHist.e0 (BHist.e1 BHist.Empty))) ∨
  (exists ledger : BHist, exists unaryLedger : UnaryHistory ledger,
    exists carries : BHistCarriesOpen T i U,
      row = BHistUnaryTopologyLedgerRow.top ledger unaryLedger carries ∧
        hsame tag (BHist.e1 (BHist.e0 BHist.Empty)))

theorem BHistUnaryTopologyLedgerRow_constructor_tag_no_confusion
    (T : BHistIndexedOpenCarrier) {i : T.OpenIx} {U : BHist -> Prop}
    (row : BHistUnaryTopologyLedgerRow T i U) :
    (BHistUnaryTopologyLedgerRow_constructorTag T row BHist.Empty ∨
      BHistUnaryTopologyLedgerRow_constructorTag T row (BHist.e0 BHist.Empty) ∨
      BHistUnaryTopologyLedgerRow_constructorTag T row (BHist.e1 BHist.Empty) ∨
      BHistUnaryTopologyLedgerRow_constructorTag T row (BHist.e0 (BHist.e0 BHist.Empty)) ∨
      BHistUnaryTopologyLedgerRow_constructorTag T row (BHist.e0 (BHist.e1 BHist.Empty)) ∨
      BHistUnaryTopologyLedgerRow_constructorTag T row (BHist.e1 (BHist.e0 BHist.Empty))) ∧
      (hsame BHist.Empty (BHist.e0 BHist.Empty) -> False) ∧
      (hsame BHist.Empty (BHist.e1 BHist.Empty) -> False) ∧
      (hsame BHist.Empty (BHist.e0 (BHist.e0 BHist.Empty)) -> False) ∧
      (hsame BHist.Empty (BHist.e0 (BHist.e1 BHist.Empty)) -> False) ∧
      (hsame BHist.Empty (BHist.e1 (BHist.e0 BHist.Empty)) -> False) ∧
      (hsame (BHist.e0 BHist.Empty) (BHist.e1 BHist.Empty) -> False) ∧
      (hsame (BHist.e0 BHist.Empty) (BHist.e0 (BHist.e0 BHist.Empty)) -> False) ∧
      (hsame (BHist.e0 BHist.Empty) (BHist.e0 (BHist.e1 BHist.Empty)) -> False) ∧
      (hsame (BHist.e0 BHist.Empty) (BHist.e1 (BHist.e0 BHist.Empty)) -> False) ∧
      (hsame (BHist.e1 BHist.Empty) (BHist.e0 (BHist.e0 BHist.Empty)) -> False) ∧
      (hsame (BHist.e1 BHist.Empty) (BHist.e0 (BHist.e1 BHist.Empty)) -> False) ∧
      (hsame (BHist.e1 BHist.Empty) (BHist.e1 (BHist.e0 BHist.Empty)) -> False) ∧
      (hsame (BHist.e0 (BHist.e0 BHist.Empty))
        (BHist.e0 (BHist.e1 BHist.Empty)) -> False) ∧
      (hsame (BHist.e0 (BHist.e0 BHist.Empty))
        (BHist.e1 (BHist.e0 BHist.Empty)) -> False) ∧
      (hsame (BHist.e0 (BHist.e1 BHist.Empty))
        (BHist.e1 (BHist.e0 BHist.Empty)) -> False) := by
  have pairwise :
      (hsame BHist.Empty (BHist.e0 BHist.Empty) -> False) ∧
      (hsame BHist.Empty (BHist.e1 BHist.Empty) -> False) ∧
      (hsame BHist.Empty (BHist.e0 (BHist.e0 BHist.Empty)) -> False) ∧
      (hsame BHist.Empty (BHist.e0 (BHist.e1 BHist.Empty)) -> False) ∧
      (hsame BHist.Empty (BHist.e1 (BHist.e0 BHist.Empty)) -> False) ∧
      (hsame (BHist.e0 BHist.Empty) (BHist.e1 BHist.Empty) -> False) ∧
      (hsame (BHist.e0 BHist.Empty) (BHist.e0 (BHist.e0 BHist.Empty)) -> False) ∧
      (hsame (BHist.e0 BHist.Empty) (BHist.e0 (BHist.e1 BHist.Empty)) -> False) ∧
      (hsame (BHist.e0 BHist.Empty) (BHist.e1 (BHist.e0 BHist.Empty)) -> False) ∧
      (hsame (BHist.e1 BHist.Empty) (BHist.e0 (BHist.e0 BHist.Empty)) -> False) ∧
      (hsame (BHist.e1 BHist.Empty) (BHist.e0 (BHist.e1 BHist.Empty)) -> False) ∧
      (hsame (BHist.e1 BHist.Empty) (BHist.e1 (BHist.e0 BHist.Empty)) -> False) ∧
      (hsame (BHist.e0 (BHist.e0 BHist.Empty))
        (BHist.e0 (BHist.e1 BHist.Empty)) -> False) ∧
      (hsame (BHist.e0 (BHist.e0 BHist.Empty))
        (BHist.e1 (BHist.e0 BHist.Empty)) -> False) ∧
      (hsame (BHist.e0 (BHist.e1 BHist.Empty))
        (BHist.e1 (BHist.e0 BHist.Empty)) -> False) := by
    constructor
    · exact not_hsame_emp_e0
    · constructor
      · exact not_hsame_emp_e1
      · constructor
        · intro same
          cases same
        · constructor
          · intro same
            cases same
          · constructor
            · intro same
              cases same
            · constructor
              · exact not_hsame_e0_e1
              · constructor
                · intro same
                  cases same
                · constructor
                  · intro same
                    cases same
                  · constructor
                    · intro same
                      cases same
                    · constructor
                      · exact not_hsame_e1_e0
                      · constructor
                        · exact not_hsame_e1_e0
                        · constructor
                          · intro same
                            cases same
                          · constructor
                            · intro same
                              cases same
                            · constructor
                              · exact not_hsame_e0_e1
                              · exact not_hsame_e0_e1
  cases row with
  | singletonMetricBall ledger unaryLedger carries =>
      have witness :
          exists ledger : BHist, exists unaryLedger : UnaryHistory ledger,
            exists carries : BHistCarriesOpen T i U,
              BHistUnaryTopologyLedgerRow.singletonMetricBall ledger unaryLedger carries =
                BHistUnaryTopologyLedgerRow.singletonMetricBall ledger unaryLedger carries ∧
                hsame BHist.Empty BHist.Empty :=
        Exists.intro ledger
          (Exists.intro unaryLedger
            (Exists.intro carries (And.intro rfl (hsame_refl BHist.Empty))))
      have tagged : BHistUnaryTopologyLedgerRow_constructorTag T
          (BHistUnaryTopologyLedgerRow.singletonMetricBall ledger unaryLedger carries) BHist.Empty :=
        Or.inl witness
      exact And.intro (Or.inl tagged) pairwise
  | finiteListIntersection ledger unaryLedger carries =>
      have witness :
          exists ledger : BHist, exists unaryLedger : UnaryHistory ledger,
            exists carries : BHistCarriesOpen T i U,
              BHistUnaryTopologyLedgerRow.finiteListIntersection ledger unaryLedger carries =
                BHistUnaryTopologyLedgerRow.finiteListIntersection ledger unaryLedger carries ∧
                hsame (BHist.e0 BHist.Empty) (BHist.e0 BHist.Empty) :=
        Exists.intro ledger
          (Exists.intro unaryLedger
            (Exists.intro carries (And.intro rfl (hsame_refl (BHist.e0 BHist.Empty)))))
      have tagged : BHistUnaryTopologyLedgerRow_constructorTag T
          (BHistUnaryTopologyLedgerRow.finiteListIntersection ledger unaryLedger carries)
          (BHist.e0 BHist.Empty) :=
        Or.inr (Or.inl witness)
      exact And.intro (Or.inr (Or.inl tagged)) pairwise
  | binaryGeneratedMeet ledger unaryLedger carries =>
      have witness :
          exists ledger : BHist, exists unaryLedger : UnaryHistory ledger,
            exists carries : BHistCarriesOpen T i U,
              BHistUnaryTopologyLedgerRow.binaryGeneratedMeet ledger unaryLedger carries =
                BHistUnaryTopologyLedgerRow.binaryGeneratedMeet ledger unaryLedger carries ∧
                hsame (BHist.e1 BHist.Empty) (BHist.e1 BHist.Empty) :=
        Exists.intro ledger
          (Exists.intro unaryLedger
            (Exists.intro carries (And.intro rfl (hsame_refl (BHist.e1 BHist.Empty)))))
      have tagged : BHistUnaryTopologyLedgerRow_constructorTag T
          (BHistUnaryTopologyLedgerRow.binaryGeneratedMeet ledger unaryLedger carries)
          (BHist.e1 BHist.Empty) :=
        Or.inr (Or.inr (Or.inl witness))
      exact And.intro (Or.inr (Or.inr (Or.inl tagged))) pairwise
  | arbitraryUnion ledger unaryLedger carries =>
      have witness :
          exists ledger : BHist, exists unaryLedger : UnaryHistory ledger,
            exists carries : BHistCarriesOpen T i U,
              BHistUnaryTopologyLedgerRow.arbitraryUnion ledger unaryLedger carries =
                BHistUnaryTopologyLedgerRow.arbitraryUnion ledger unaryLedger carries ∧
                hsame (BHist.e0 (BHist.e0 BHist.Empty))
                  (BHist.e0 (BHist.e0 BHist.Empty)) :=
        Exists.intro ledger
          (Exists.intro unaryLedger
            (Exists.intro carries
              (And.intro rfl (hsame_refl (BHist.e0 (BHist.e0 BHist.Empty))))))
      have tagged : BHistUnaryTopologyLedgerRow_constructorTag T
          (BHistUnaryTopologyLedgerRow.arbitraryUnion ledger unaryLedger carries)
          (BHist.e0 (BHist.e0 BHist.Empty)) :=
        Or.inr (Or.inr (Or.inr (Or.inl witness)))
      exact And.intro (Or.inr (Or.inr (Or.inr (Or.inl tagged)))) pairwise
  | bottom ledger unaryLedger carries =>
      have witness :
          exists ledger : BHist, exists unaryLedger : UnaryHistory ledger,
            exists carries : BHistCarriesOpen T i U,
              BHistUnaryTopologyLedgerRow.bottom ledger unaryLedger carries =
                BHistUnaryTopologyLedgerRow.bottom ledger unaryLedger carries ∧
                hsame (BHist.e0 (BHist.e1 BHist.Empty))
                  (BHist.e0 (BHist.e1 BHist.Empty)) :=
        Exists.intro ledger
          (Exists.intro unaryLedger
            (Exists.intro carries
              (And.intro rfl (hsame_refl (BHist.e0 (BHist.e1 BHist.Empty))))))
      have tagged : BHistUnaryTopologyLedgerRow_constructorTag T
          (BHistUnaryTopologyLedgerRow.bottom ledger unaryLedger carries)
          (BHist.e0 (BHist.e1 BHist.Empty)) :=
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inl witness))))
      exact And.intro (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl tagged))))) pairwise
  | top ledger unaryLedger carries =>
      have witness :
          exists ledger : BHist, exists unaryLedger : UnaryHistory ledger,
            exists carries : BHistCarriesOpen T i U,
              BHistUnaryTopologyLedgerRow.top ledger unaryLedger carries =
                BHistUnaryTopologyLedgerRow.top ledger unaryLedger carries ∧
                hsame (BHist.e1 (BHist.e0 BHist.Empty))
                  (BHist.e1 (BHist.e0 BHist.Empty)) :=
        Exists.intro ledger
          (Exists.intro unaryLedger
            (Exists.intro carries
              (And.intro rfl (hsame_refl (BHist.e1 (BHist.e0 BHist.Empty))))))
      have tagged : BHistUnaryTopologyLedgerRow_constructorTag T
          (BHistUnaryTopologyLedgerRow.top ledger unaryLedger carries)
          (BHist.e1 (BHist.e0 BHist.Empty)) :=
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr witness))))
      exact And.intro (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr tagged))))) pairwise

theorem BHistIndexedOpen_neighborhood_semantic_name_certificate
    (T : BHistIndexedOpenCarrier) {i : T.OpenIx}
    (source : exists h : BHist, UnaryHistory h ∧ T.OpenAt i h) :
    SemanticNameCert (fun h : BHist => UnaryHistory h ∧ T.OpenAt i h)
      (fun h : BHist => T.OpenAt i h) (fun h : BHist => T.OpenAt i h)
      (fun h k : BHist => UnaryHistory h ∧ UnaryHistory k ∧ hsame h k) := by
  exact {
    core := {
      carrier_inhabited := source
      equiv_refl := by
        intro h sourceH
        exact And.intro sourceH.left (And.intro sourceH.left (hsame_refl h))
      equiv_symm := by
        intro h k classified
        exact And.intro classified.right.left
          (And.intro classified.left (hsame_symm classified.right.right))
      equiv_trans := by
        intro h k r classifiedHK classifiedKR
        exact And.intro classifiedHK.left
          (And.intro classifiedKR.right.left
            (hsame_trans classifiedHK.right.right classifiedKR.right.right))
      carrier_respects_equiv := by
        intro h k classified sourceH
        have stable : T.OpenAt i h <-> T.OpenAt i k :=
          T.membership_stable sourceH.left classified.right.left classified.right.right
        exact And.intro classified.right.left (Iff.mp stable sourceH.right)
    }
    pattern_sound := by
      intro h sourceH
      exact sourceH.right
    ledger_sound := by
      intro h sourceH
      exact sourceH.right
  }

theorem TopologyScopedObligation_downstream_export_certificate
    (T : BHistIndexedOpenCarrier) {i : T.OpenIx} {U : BHist -> Prop} {ledger : BHist}
    (tree : BHistLedgerPublicOpenTree T i U ledger)
    (source : exists h : BHist, UnaryHistory h ∧ U h) :
    SemanticNameCert (fun h : BHist => UnaryHistory h ∧ U h)
      (fun h : BHist => T.OpenAt i h)
      (fun h : BHist => BHistLedgerPublicOpenTree T i U ledger ∧ T.OpenAt i h)
      (fun h k : BHist => UnaryHistory h ∧ UnaryHistory k ∧ hsame h k) ∧
      BHistCarriesOpen T i U ∧ BHistGeneratedOpenExact T U ∧
        (forall {x y : BHist}, UnaryHistory x -> UnaryHistory y -> hsame x y ->
          (U x <-> U y)) ∧
          ((hsame ledger ledger) ∨
            (exists leftLedger : BHist, exists rightLedger : BHist,
              hsame ledger (BHist.e0 (append leftLedger rightLedger))) ∨
            hsame ledger (BHist.e1 BHist.Empty) ∨ hsame ledger (BHist.e0 BHist.Empty)) := by
  have carries : BHistCarriesOpen T i U :=
    BHistPublicOpenTree_carries_open T tree
  have generated : BHistGeneratedOpenExact T U :=
    Exists.intro i carries
  have classifierTransport :
      forall {x y : BHist}, UnaryHistory x -> UnaryHistory y -> hsame x y ->
        (U x <-> U y) :=
    BHistCarriesOpen_classifier_transport T carries
  have cert :
      SemanticNameCert (fun h : BHist => UnaryHistory h ∧ U h)
        (fun h : BHist => T.OpenAt i h)
        (fun h : BHist => BHistLedgerPublicOpenTree T i U ledger ∧ T.OpenAt i h)
        (fun h k : BHist => UnaryHistory h ∧ UnaryHistory k ∧ hsame h k) := {
    core := {
      carrier_inhabited := source
      equiv_refl := by
        intro h sourceH
        exact And.intro sourceH.left (And.intro sourceH.left (hsame_refl h))
      equiv_symm := by
        intro h k classified
        exact And.intro classified.right.left
          (And.intro classified.left (hsame_symm classified.right.right))
      equiv_trans := by
        intro h k r classifiedHK classifiedKR
        exact And.intro classifiedHK.left
          (And.intro classifiedKR.right.left
            (hsame_trans classifiedHK.right.right classifiedKR.right.right))
      carrier_respects_equiv := by
        intro h k classified sourceH
        have stable : U h <-> U k :=
          classifierTransport sourceH.left classified.right.left classified.right.right
        exact And.intro classified.right.left (Iff.mp stable sourceH.right)
    }
    pattern_sound := by
      intro h sourceH
      have carried : U h <-> T.OpenAt i h :=
        carries sourceH.left
      exact Iff.mp carried sourceH.right
    ledger_sound := by
      intro h sourceH
      have carried : U h <-> T.OpenAt i h :=
        carries sourceH.left
      exact And.intro tree (Iff.mp carried sourceH.right)
  }
  have ledgerCoverage :
      (hsame ledger ledger) ∨
        (exists leftLedger : BHist, exists rightLedger : BHist,
          hsame ledger (BHist.e0 (append leftLedger rightLedger))) ∨
        hsame ledger (BHist.e1 BHist.Empty) ∨ hsame ledger (BHist.e0 BHist.Empty) := by
    cases tree with
    | base carries =>
        exact Or.inl (hsame_refl ledger)
    | meet leftTree rightTree =>
        exact Or.inr (Or.inl
          (Exists.intro _
            (Exists.intro _ (hsame_refl (BHist.e0 (append _ _))))))
    | union subtrees unionLaw =>
        exact Or.inr (Or.inr (Or.inl (hsame_refl (BHist.e1 BHist.Empty))))
    | bottom boundary =>
        exact Or.inr (Or.inr (Or.inr (hsame_refl (BHist.e0 BHist.Empty))))
    | top boundary =>
        exact Or.inr (Or.inr (Or.inl (hsame_refl (BHist.e1 BHist.Empty))))
  exact And.intro cert
    (And.intro carries
      (And.intro generated
        (And.intro classifierTransport ledgerCoverage)))


theorem BHistFiniteBaseNeighborhood_bundleAppend_carries_intersection
    (T : BHistIndexedOpenCarrier) (left right : ProbeBundle BHist)
    (ball : BHist -> BHist -> Prop) {i j : T.OpenIx} :
    BHistCarriesOpen T i (BHistFiniteBaseNeighborhood left ball) ->
      BHistCarriesOpen T j (BHistFiniteBaseNeighborhood right ball) ->
        BHistCarriesOpen T (T.meet i j)
          (BHistFiniteBaseNeighborhood (bundleAppend left right) ball) := by
  intro carryLeft carryRight x unaryX
  have closure :
      BHistCarriesOpen T (T.meet i j)
          (fun x : BHist =>
            BHistFiniteBaseNeighborhood left ball x ∧
              BHistFiniteBaseNeighborhood right ball x) ∧
        (forall {x y : BHist}, UnaryHistory x -> UnaryHistory y -> hsame x y ->
          ((BHistFiniteBaseNeighborhood left ball x ∧
              BHistFiniteBaseNeighborhood right ball x) <->
            (BHistFiniteBaseNeighborhood left ball y ∧
              BHistFiniteBaseNeighborhood right ball y))) :=
    BHistIndexedOpen_finite_intersection_closure (T := T) (i := i) (j := j)
      (U := fun x : BHist => BHistFiniteBaseNeighborhood left ball x)
      (V := fun x : BHist => BHistFiniteBaseNeighborhood right ball x) carryLeft
      carryRight
  have meetClosure :
      BHistCarriesOpen T (T.meet i j)
        (fun x : BHist =>
          BHistFiniteBaseNeighborhood left ball x ∧
            BHistFiniteBaseNeighborhood right ball x) :=
    closure.left
  have appendSplit :
      BHistFiniteBaseNeighborhood (bundleAppend left right) ball x <->
        BHistFiniteBaseNeighborhood left ball x ∧
          BHistFiniteBaseNeighborhood right ball x := by
    constructor
    · intro appendNeighborhood
      constructor
      · intro p memberLeft
        have memberAppend : InBundle p (bundleAppend left right) :=
          Iff.mpr (inBundle_bundleAppend_iff (p := p) (left := left) (right := right))
            (Or.inl memberLeft)
        exact appendNeighborhood p memberAppend
      · intro p memberRight
        have memberAppend : InBundle p (bundleAppend left right) :=
          Iff.mpr (inBundle_bundleAppend_iff (p := p) (left := left) (right := right))
            (Or.inr memberRight)
        exact appendNeighborhood p memberAppend
    · intro both p memberAppend
      cases Iff.mp (inBundle_bundleAppend_iff (p := p) (left := left) (right := right))
          memberAppend with
      | inl memberLeft =>
          exact both.left p memberLeft
      | inr memberRight =>
          exact both.right p memberRight
  have meetCarries :
      (BHistFiniteBaseNeighborhood left ball x ∧
          BHistFiniteBaseNeighborhood right ball x) <->
        T.OpenAt (T.meet i j) x :=
    meetClosure unaryX
  constructor
  · intro appendNeighborhood
    exact Iff.mp meetCarries (Iff.mp appendSplit appendNeighborhood)
  · intro openMeet
    exact Iff.mpr appendSplit (Iff.mpr meetCarries openMeet)

theorem BHistFiniteBaseNeighborhoodCarrier_metric_generated_namecert_surface
    (ball : BHist -> BHist -> Prop)
    (ballStable :
      forall {indices : ProbeBundle BHist} {i x y : BHist}, InBundle i indices ->
        UnaryHistory x -> UnaryHistory y -> hsame x y -> (ball i x <-> ball i y))
    {indices : ProbeBundle BHist} {ledger : BHist} (unaryLedger : UnaryHistory ledger) :
    BHistUnaryTopologyLedgerRow (BHistFiniteBaseNeighborhoodCarrier ball ballStable) indices
        (BHistFiniteBaseNeighborhood indices ball) ∧
      BHistGeneratedOpenExact (BHistFiniteBaseNeighborhoodCarrier ball ballStable)
        (BHistFiniteBaseNeighborhood indices ball) ∧
        (forall {x y : BHist}, UnaryHistory x -> UnaryHistory y -> hsame x y ->
          (BHistFiniteBaseNeighborhood indices ball x <->
            BHistFiniteBaseNeighborhood indices ball y)) ∧
          (forall {left right : ProbeBundle BHist},
            (BHistFiniteBaseNeighborhoodCarrier ball ballStable).meet left right =
              bundleAppend left right) := by
  let T : BHistIndexedOpenCarrier := BHistFiniteBaseNeighborhoodCarrier ball ballStable
  have carries : BHistCarriesOpen T indices (BHistFiniteBaseNeighborhood indices ball) := by
    intro x _unaryX
    constructor
    · intro neighborhood
      exact neighborhood
    · intro openAt
      exact openAt
  have row :
      BHistUnaryTopologyLedgerRow T indices (BHistFiniteBaseNeighborhood indices ball) :=
    BHistUnaryTopologyLedgerRow.singletonMetricBall ledger unaryLedger carries
  have generated :
      BHistGeneratedOpenExact T (BHistFiniteBaseNeighborhood indices ball) :=
    Exists.intro indices carries
  have transport :
      forall {x y : BHist}, UnaryHistory x -> UnaryHistory y -> hsame x y ->
        (BHistFiniteBaseNeighborhood indices ball x <->
          BHistFiniteBaseNeighborhood indices ball y) := by
    intro x y unaryX unaryY sameXY
    exact T.membership_stable unaryX unaryY sameXY
  have meetEquation :
      forall {left right : ProbeBundle BHist}, T.meet left right = bundleAppend left right := by
    intro left right
    rfl
  exact And.intro row (And.intro generated (And.intro transport meetEquation))

theorem BHistLedgerPublicOpenTree_meet_ledger_constructor (T : BHistIndexedOpenCarrier)
    {i j : T.OpenIx} {U V : BHist -> Prop} {leftLedger rightLedger : BHist} :
    BHistLedgerPublicOpenTree T i U leftLedger ->
      BHistLedgerPublicOpenTree T j V rightLedger ->
        BHistLedgerPublicOpenTree T (T.meet i j) (fun x : BHist => U x ∧ V x)
            (BHist.e0 (append leftLedger rightLedger)) ∧
          BHistCarriesOpen T (T.meet i j) (fun x : BHist => U x ∧ V x) := by
  intro leftTree rightTree
  have meetTree :
      BHistLedgerPublicOpenTree T (T.meet i j) (fun x : BHist => U x ∧ V x)
        (BHist.e0 (append leftLedger rightLedger)) :=
    BHistLedgerPublicOpenTree.meet leftTree rightTree
  exact And.intro meetTree (BHistPublicOpenTree_carries_open T meetTree)

theorem BHistLedgerGeneratedOpen_row_coverage (T : BHistIndexedOpenCarrier)
    {i : T.OpenIx} {U : BHist -> Prop} {ledger : BHist} :
    BHistLedgerPublicOpenTree T i U ledger ->
      BHistGeneratedOpenExact T U ∧ BHistCarriesOpen T i U ∧
        (exists r : BHist, BHistLedgerPublicOpenTree T i U r) ∧
          (forall {x y : BHist}, UnaryHistory x -> UnaryHistory y -> hsame x y ->
            (U x <-> U y)) := by
  intro tree
  have carries : BHistCarriesOpen T i U :=
    BHistPublicOpenTree_carries_open T tree
  exact And.intro (Exists.intro i carries)
    (And.intro carries
      (And.intro (Exists.intro ledger tree)
        (BHistCarriesOpen_classifier_transport T carries)))

theorem BHistUnaryTopologyDepsReady_obligation_package (T : BHistIndexedOpenCarrier)
    {i j : T.OpenIx} {U V : BHist -> Prop} :
    BHistUnaryTopologyLedgerRow T i U -> BHistUnaryTopologyLedgerRow T j V ->
      (forall {x y : BHist}, UnaryHistory x -> UnaryHistory y -> hsame x y ->
        (U x <-> U y)) ∧
        BHistCarriesOpen T (T.meet i j) (fun x : BHist => U x ∧ V x) ∧
          (exists ledger : BHist, UnaryHistory ledger) := by
  intro rowU rowV
  have transportU :
      forall {x y : BHist}, UnaryHistory x -> UnaryHistory y -> hsame x y ->
        (U x <-> U y) :=
    BHistUnaryTopologyLedgerRow_classifier_transport T rowU
  have carriesU : BHistCarriesOpen T i U := by
    cases rowU with
    | singletonMetricBall _ _ carries => exact carries
    | finiteListIntersection _ _ carries => exact carries
    | binaryGeneratedMeet _ _ carries => exact carries
    | arbitraryUnion _ _ carries => exact carries
    | bottom _ _ carries => exact carries
    | top _ _ carries => exact carries
  have carriesV : BHistCarriesOpen T j V := by
    cases rowV with
    | singletonMetricBall _ _ carries => exact carries
    | finiteListIntersection _ _ carries => exact carries
    | binaryGeneratedMeet _ _ carries => exact carries
    | arbitraryUnion _ _ carries => exact carries
    | bottom _ _ carries => exact carries
    | top _ _ carries => exact carries
  have meetClosure :
      BHistCarriesOpen T (T.meet i j) (fun x : BHist => U x ∧ V x) :=
    (BHistIndexedOpen_finite_intersection_closure T carriesU carriesV).left
  have ledgerWitness : exists ledger : BHist, UnaryHistory ledger := by
    cases rowU with
    | singletonMetricBall ledger unaryLedger _ => exact Exists.intro ledger unaryLedger
    | finiteListIntersection ledger unaryLedger _ => exact Exists.intro ledger unaryLedger
    | binaryGeneratedMeet ledger unaryLedger _ => exact Exists.intro ledger unaryLedger
    | arbitraryUnion ledger unaryLedger _ => exact Exists.intro ledger unaryLedger
    | bottom ledger unaryLedger _ => exact Exists.intro ledger unaryLedger
    | top ledger unaryLedger _ => exact Exists.intro ledger unaryLedger
  exact And.intro transportU (And.intro meetClosure ledgerWitness)

theorem BHistUnaryTopologyLedgerRow_metric_generated_obligation_surface
    (T : BHistIndexedOpenCarrier) {i j : T.OpenIx} {U V : BHist -> Prop} :
    BHistUnaryTopologyLedgerRow T i U -> BHistUnaryTopologyLedgerRow T j V ->
      (BHistGeneratedOpenExact T U ∧
          (forall {x y : BHist}, UnaryHistory x -> UnaryHistory y -> hsame x y ->
            (U x <-> U y))) ∧
        (BHistGeneratedOpenExact T V ∧
          (forall {x y : BHist}, UnaryHistory x -> UnaryHistory y -> hsame x y ->
            (V x <-> V y))) ∧
        BHistCarriesOpen T (T.meet i j) (fun x : BHist => U x ∧ V x) ∧
        BHistGeneratedOpenExact T (fun x : BHist => U x ∧ V x) ∧
        (exists ledger : BHist, UnaryHistory ledger) := by
  intro rowU rowV
  have transportU :
      forall {x y : BHist}, UnaryHistory x -> UnaryHistory y -> hsame x y ->
        (U x <-> U y) :=
    BHistUnaryTopologyLedgerRow_classifier_transport T rowU
  have transportV :
      forall {x y : BHist}, UnaryHistory x -> UnaryHistory y -> hsame x y ->
        (V x <-> V y) :=
    BHistUnaryTopologyLedgerRow_classifier_transport T rowV
  have carriesU : BHistCarriesOpen T i U := by
    cases rowU with
    | singletonMetricBall _ _ carries => exact carries
    | finiteListIntersection _ _ carries => exact carries
    | binaryGeneratedMeet _ _ carries => exact carries
    | arbitraryUnion _ _ carries => exact carries
    | bottom _ _ carries => exact carries
    | top _ _ carries => exact carries
  have carriesV : BHistCarriesOpen T j V := by
    cases rowV with
    | singletonMetricBall _ _ carries => exact carries
    | finiteListIntersection _ _ carries => exact carries
    | binaryGeneratedMeet _ _ carries => exact carries
    | arbitraryUnion _ _ carries => exact carries
    | bottom _ _ carries => exact carries
    | top _ _ carries => exact carries
  have meetClosure :=
    BHistIndexedOpen_finite_intersection_closure (T := T) (i := i) (j := j)
      (U := U) (V := V) carriesU carriesV
  have exactU : BHistGeneratedOpenExact T U :=
    Exists.intro i carriesU
  have exactV : BHistGeneratedOpenExact T V :=
    Exists.intro j carriesV
  have exactMeet : BHistGeneratedOpenExact T (fun x : BHist => U x ∧ V x) :=
    Exists.intro (T.meet i j) meetClosure.left
  have ledgerWitness : exists ledger : BHist, UnaryHistory ledger := by
    cases rowU with
    | singletonMetricBall ledger unaryLedger _ => exact Exists.intro ledger unaryLedger
    | finiteListIntersection ledger unaryLedger _ => exact Exists.intro ledger unaryLedger
    | binaryGeneratedMeet ledger unaryLedger _ => exact Exists.intro ledger unaryLedger
    | arbitraryUnion ledger unaryLedger _ => exact Exists.intro ledger unaryLedger
    | bottom ledger unaryLedger _ => exact Exists.intro ledger unaryLedger
    | top ledger unaryLedger _ => exact Exists.intro ledger unaryLedger
  exact And.intro (And.intro exactU transportU)
    (And.intro (And.intro exactV transportV)
      (And.intro meetClosure.left (And.intro exactMeet ledgerWitness)))

theorem BHistFiniteBaseNeighborhood_singleton_ledger_coverage
    (T : BHistIndexedOpenCarrier) (ball : BHist -> BHist -> Prop)
    {center ledger : BHist} {i : T.OpenIx}
    (unaryLedger : UnaryHistory ledger)
    (carries : BHistCarriesOpen T i (fun x : BHist => ball center x))
    (ballStable :
      forall {x y : BHist},
        UnaryHistory x -> UnaryHistory y -> hsame x y -> (ball center x <-> ball center y)) :
    BHistUnaryTopologyLedgerRow T i
        (BHistFiniteBaseNeighborhood
          (ProbeBundle.Bcons center (ProbeBundle.Bnil : ProbeBundle BHist)) ball) ∧
      BHistGeneratedOpenExact T
        (BHistFiniteBaseNeighborhood
          (ProbeBundle.Bcons center (ProbeBundle.Bnil : ProbeBundle BHist)) ball) ∧
        (forall {x y : BHist}, UnaryHistory x -> UnaryHistory y -> hsame x y ->
          (BHistFiniteBaseNeighborhood
              (ProbeBundle.Bcons center (ProbeBundle.Bnil : ProbeBundle BHist)) ball x <->
            BHistFiniteBaseNeighborhood
              (ProbeBundle.Bcons center (ProbeBundle.Bnil : ProbeBundle BHist)) ball y)) := by
  let singleton : ProbeBundle BHist :=
    ProbeBundle.Bcons center (ProbeBundle.Bnil : ProbeBundle BHist)
  have singletonCarries :
      BHistCarriesOpen T i (BHistFiniteBaseNeighborhood singleton ball) := by
    intro x unaryX
    have carryCenter : ball center x <-> T.OpenAt i x :=
      carries unaryX
    constructor
    · intro neighborhood
      exact Iff.mp carryCenter (neighborhood center (Or.inl rfl))
    · intro openAt p inSingleton
      cases inSingleton with
      | inl samePCenter =>
          cases samePCenter
          exact Iff.mpr carryCenter openAt
      | inr inNil =>
          cases inNil
  have singletonStable :
      forall {b x y : BHist}, InBundle b singleton -> UnaryHistory x -> UnaryHistory y ->
        hsame x y -> (ball b x <-> ball b y) := by
    intro b x y inSingleton unaryX unaryY sameXY
    cases inSingleton with
    | inl sameBCenter =>
        cases sameBCenter
        exact ballStable unaryX unaryY sameXY
    | inr inNil =>
        cases inNil
  constructor
  · exact BHistUnaryTopologyLedgerRow.singletonMetricBall ledger unaryLedger singletonCarries
  · constructor
    · exact Exists.intro i singletonCarries
    · exact BHistFiniteBaseNeighborhood_classifier_transport singleton ball singletonStable

theorem TopologySingleton_public_open_row_coverage :
    (BHistUnaryTopologyLedgerRow TopologySingletonIndexedOpenCarrier (BHist.e0 BHist.Empty)
        (fun _ : BHist => False) ∧
      BHistCarriesOpen TopologySingletonIndexedOpenCarrier (BHist.e0 BHist.Empty)
        (fun _ : BHist => False)) ∧
    (BHistUnaryTopologyLedgerRow TopologySingletonIndexedOpenCarrier BHist.Empty
        TopologySingletonCarrier ∧
      BHistCarriesOpen TopologySingletonIndexedOpenCarrier BHist.Empty
        TopologySingletonCarrier) := by
  have boundaryRows := TopologySingleton_semantic_name_certificate.right
  have bottomLaw :
      forall h : BHist, TopologySingletonOpenAt (BHist.e0 BHist.Empty) h <-> False :=
    boundaryRows.left
  have topLaw :
      forall h : BHist, TopologySingletonOpenAt BHist.Empty h <-> TopologySingletonCarrier h :=
    boundaryRows.right
  have bottomCarries :
      BHistCarriesOpen TopologySingletonIndexedOpenCarrier (BHist.e0 BHist.Empty)
        (fun _ : BHist => False) := by
    intro x _unaryX
    have bottomAt : TopologySingletonOpenAt (BHist.e0 BHist.Empty) x <-> False :=
      bottomLaw x
    constructor
    · intro impossible
      exact False.elim impossible
    · intro openBottom
      exact Iff.mp bottomAt openBottom
  have topCarries :
      BHistCarriesOpen TopologySingletonIndexedOpenCarrier BHist.Empty
        TopologySingletonCarrier := by
    intro x _unaryX
    have topAt : TopologySingletonOpenAt BHist.Empty x <-> TopologySingletonCarrier x :=
      topLaw x
    constructor
    · intro carrierX
      exact Iff.mpr topAt carrierX
    · intro openTop
      exact Iff.mp topAt openTop
  have bottomRow :
      BHistUnaryTopologyLedgerRow TopologySingletonIndexedOpenCarrier (BHist.e0 BHist.Empty)
        (fun _ : BHist => False) :=
    BHistUnaryTopologyLedgerRow.bottom BHist.Empty unary_empty bottomCarries
  have topRow :
      BHistUnaryTopologyLedgerRow TopologySingletonIndexedOpenCarrier BHist.Empty
        TopologySingletonCarrier :=
    BHistUnaryTopologyLedgerRow.top BHist.Empty unary_empty topCarries
  exact And.intro (And.intro bottomRow bottomCarries) (And.intro topRow topCarries)

theorem BHistGeneratedOpenExact_public_open_witness (T : BHistIndexedOpenCarrier)
    {U : BHist -> Prop} :
    BHistGeneratedOpenExact T U ->
      exists i : T.OpenIx, exists ledger : BHist,
        hsame ledger BHist.Empty ∧ BHistCarriesOpen T i U ∧ TopologyPublicOpenTree T i U := by
  intro generated
  cases generated with
  | intro i carries =>
      exact Exists.intro i
        (Exists.intro BHist.Empty
          (And.intro (hsame_refl BHist.Empty)
            (And.intro carries (TopologyPublicOpenTree.basic carries))))

end BEDC.Derived.TopologyUp
