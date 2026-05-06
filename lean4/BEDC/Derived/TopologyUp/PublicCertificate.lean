import BEDC.Derived.TopologyUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.TopologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem BHistUnaryTopologyLedgerRow_semantic_name_certificate (T : BHistIndexedOpenCarrier)
    {i : T.OpenIx} {U : BHist -> Prop} (row : BHistUnaryTopologyLedgerRow T i U)
    (source : exists h : BHist, UnaryHistory h ∧ U h) :
    SemanticNameCert (fun h : BHist => UnaryHistory h ∧ U h)
      (fun h : BHist => T.OpenAt i h)
      (fun h : BHist =>
        exists ledger : BHist,
          UnaryHistory ledger ∧ BHistUnaryTopologyLedgerRow T i U ∧ T.OpenAt i h)
      (fun h k : BHist => UnaryHistory h ∧ UnaryHistory k ∧ hsame h k) := by
  cases row with
  | singletonMetricBall ledger unaryLedger carries =>
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
            have carryH : U h <-> T.OpenAt i h := carries sourceH.left
            have carryK : U k <-> T.OpenAt i k := carries classified.right.left
            have stable : T.OpenAt i h <-> T.OpenAt i k :=
              T.membership_stable sourceH.left classified.right.left classified.right.right
            have openH : T.OpenAt i h := Iff.mp carryH sourceH.right
            exact And.intro classified.right.left (Iff.mpr carryK (Iff.mp stable openH))
        }
        pattern_sound := by
          intro h sourceH
          exact Iff.mp (carries sourceH.left) sourceH.right
        ledger_sound := by
          intro h sourceH
          exact
            Exists.intro ledger
              (And.intro unaryLedger
                (And.intro
                  (BHistUnaryTopologyLedgerRow.singletonMetricBall ledger unaryLedger carries)
                  (Iff.mp (carries sourceH.left) sourceH.right)))
      }
  | finiteListIntersection ledger unaryLedger carries =>
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
            have carryH : U h <-> T.OpenAt i h := carries sourceH.left
            have carryK : U k <-> T.OpenAt i k := carries classified.right.left
            have stable : T.OpenAt i h <-> T.OpenAt i k :=
              T.membership_stable sourceH.left classified.right.left classified.right.right
            have openH : T.OpenAt i h := Iff.mp carryH sourceH.right
            exact And.intro classified.right.left (Iff.mpr carryK (Iff.mp stable openH))
        }
        pattern_sound := by
          intro h sourceH
          exact Iff.mp (carries sourceH.left) sourceH.right
        ledger_sound := by
          intro h sourceH
          exact
            Exists.intro ledger
              (And.intro unaryLedger
                (And.intro
                  (BHistUnaryTopologyLedgerRow.finiteListIntersection ledger unaryLedger carries)
                  (Iff.mp (carries sourceH.left) sourceH.right)))
      }
  | binaryGeneratedMeet ledger unaryLedger carries =>
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
            have carryH : U h <-> T.OpenAt i h := carries sourceH.left
            have carryK : U k <-> T.OpenAt i k := carries classified.right.left
            have stable : T.OpenAt i h <-> T.OpenAt i k :=
              T.membership_stable sourceH.left classified.right.left classified.right.right
            have openH : T.OpenAt i h := Iff.mp carryH sourceH.right
            exact And.intro classified.right.left (Iff.mpr carryK (Iff.mp stable openH))
        }
        pattern_sound := by
          intro h sourceH
          exact Iff.mp (carries sourceH.left) sourceH.right
        ledger_sound := by
          intro h sourceH
          exact
            Exists.intro ledger
              (And.intro unaryLedger
                (And.intro
                  (BHistUnaryTopologyLedgerRow.binaryGeneratedMeet ledger unaryLedger carries)
                  (Iff.mp (carries sourceH.left) sourceH.right)))
      }
  | arbitraryUnion ledger unaryLedger carries =>
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
            have carryH : U h <-> T.OpenAt i h := carries sourceH.left
            have carryK : U k <-> T.OpenAt i k := carries classified.right.left
            have stable : T.OpenAt i h <-> T.OpenAt i k :=
              T.membership_stable sourceH.left classified.right.left classified.right.right
            have openH : T.OpenAt i h := Iff.mp carryH sourceH.right
            exact And.intro classified.right.left (Iff.mpr carryK (Iff.mp stable openH))
        }
        pattern_sound := by
          intro h sourceH
          exact Iff.mp (carries sourceH.left) sourceH.right
        ledger_sound := by
          intro h sourceH
          exact
            Exists.intro ledger
              (And.intro unaryLedger
                (And.intro
                  (BHistUnaryTopologyLedgerRow.arbitraryUnion ledger unaryLedger carries)
                  (Iff.mp (carries sourceH.left) sourceH.right)))
      }
  | bottom ledger unaryLedger carries =>
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
            have carryH : U h <-> T.OpenAt i h := carries sourceH.left
            have carryK : U k <-> T.OpenAt i k := carries classified.right.left
            have stable : T.OpenAt i h <-> T.OpenAt i k :=
              T.membership_stable sourceH.left classified.right.left classified.right.right
            have openH : T.OpenAt i h := Iff.mp carryH sourceH.right
            exact And.intro classified.right.left (Iff.mpr carryK (Iff.mp stable openH))
        }
        pattern_sound := by
          intro h sourceH
          exact Iff.mp (carries sourceH.left) sourceH.right
        ledger_sound := by
          intro h sourceH
          exact
            Exists.intro ledger
              (And.intro unaryLedger
                (And.intro
                  (BHistUnaryTopologyLedgerRow.bottom ledger unaryLedger carries)
                  (Iff.mp (carries sourceH.left) sourceH.right)))
      }
  | top ledger unaryLedger carries =>
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
            have carryH : U h <-> T.OpenAt i h := carries sourceH.left
            have carryK : U k <-> T.OpenAt i k := carries classified.right.left
            have stable : T.OpenAt i h <-> T.OpenAt i k :=
              T.membership_stable sourceH.left classified.right.left classified.right.right
            have openH : T.OpenAt i h := Iff.mp carryH sourceH.right
            exact And.intro classified.right.left (Iff.mpr carryK (Iff.mp stable openH))
        }
        pattern_sound := by
          intro h sourceH
          exact Iff.mp (carries sourceH.left) sourceH.right
        ledger_sound := by
          intro h sourceH
          exact
            Exists.intro ledger
              (And.intro unaryLedger
                (And.intro (BHistUnaryTopologyLedgerRow.top ledger unaryLedger carries)
                  (Iff.mp (carries sourceH.left) sourceH.right)))
      }

theorem BHistLedgerPublicOpenTree_semantic_name_certificate (T : BHistIndexedOpenCarrier)
    {i : T.OpenIx} {U : BHist -> Prop} {ledger : BHist}
    (tree : BHistLedgerPublicOpenTree T i U ledger)
    (source : exists h : BHist, UnaryHistory h ∧ U h) :
    SemanticNameCert (fun h : BHist => UnaryHistory h ∧ U h)
      (fun h : BHist => T.OpenAt i h)
      (fun h : BHist => BHistLedgerPublicOpenTree T i U ledger ∧ T.OpenAt i h)
      (fun h k : BHist => UnaryHistory h ∧ UnaryHistory k ∧ hsame h k) := by
  have carries : BHistCarriesOpen T i U := BHistPublicOpenTree_carries_open T tree
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
        have carryH : U h <-> T.OpenAt i h := carries sourceH.left
        have carryK : U k <-> T.OpenAt i k := carries classified.right.left
        have stable : T.OpenAt i h <-> T.OpenAt i k :=
          T.membership_stable sourceH.left classified.right.left classified.right.right
        have openH : T.OpenAt i h := Iff.mp carryH sourceH.right
        exact And.intro classified.right.left (Iff.mpr carryK (Iff.mp stable openH))
    }
    pattern_sound := by
      intro h sourceH
      exact Iff.mp (carries sourceH.left) sourceH.right
    ledger_sound := by
      intro h sourceH
      exact And.intro tree (Iff.mp (carries sourceH.left) sourceH.right)
  }

theorem BHistLedgerPublicOpenTree_downstream_export_surface
    (T : BHistIndexedOpenCarrier) {i : T.OpenIx} {U : BHist -> Prop} {ledger : BHist}
    (tree : BHistLedgerPublicOpenTree T i U ledger)
    (source : exists h : BHist, UnaryHistory h ∧ U h) :
    SemanticNameCert (fun h : BHist => UnaryHistory h ∧ U h)
      (fun h : BHist => T.OpenAt i h)
      (fun h : BHist => BHistLedgerPublicOpenTree T i U ledger ∧ T.OpenAt i h)
      (fun h k : BHist => UnaryHistory h ∧ UnaryHistory k ∧ hsame h k) ∧
    BHistCarriesOpen T i U ∧
    (forall {x y : BHist}, UnaryHistory x -> UnaryHistory y -> hsame x y -> (U x <-> U y)) := by
  have carries : BHistCarriesOpen T i U := BHistPublicOpenTree_carries_open T tree
  exact And.intro (BHistLedgerPublicOpenTree_semantic_name_certificate T tree source)
    (And.intro carries
      (BHistPublicOpenTree_unary_membership_transport T tree))

end BEDC.Derived.TopologyUp
