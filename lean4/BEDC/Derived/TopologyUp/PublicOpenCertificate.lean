import BEDC.Derived.TopologyUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.TopologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem TopologyPublicOpenTree_semantic_name_certificate (T : BHistIndexedOpenCarrier)
    {i : T.OpenIx} {U : BHist -> Prop} (tree : TopologyPublicOpenTree T i U)
    (source : exists h : BHist, UnaryHistory h ∧ U h) :
    SemanticNameCert (fun h : BHist => UnaryHistory h ∧ U h)
      (fun h : BHist => T.OpenAt i h)
      (fun h : BHist => T.OpenAt i h)
      (fun h k : BHist => UnaryHistory h ∧ UnaryHistory k ∧ hsame h k) := by
  have carries : BHistCarriesOpen T i U := by
    clear source
    induction tree with
    | basic carried =>
        exact carried
    | binaryMeet leftTree rightTree leftCarries rightCarries =>
        exact (BHistIndexedOpen_finite_intersection_closure T leftCarries rightCarries).left
    | arbitraryUnion children unionLaw childCarries =>
        exact (BHistIndexedOpen_arbitrary_union_closure T unionLaw childCarries).left
    | bottom boundary =>
        exact (BHistIndexedOpen_boundary_closure T boundary).left
    | top boundary =>
        exact (BHistIndexedOpen_boundary_closure T boundary).right.left
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
        have openK : T.OpenAt i k := Iff.mp stable openH
        exact And.intro classified.right.left (Iff.mpr carryK openK)
    }
    pattern_sound := by
      intro h sourceH
      have carryH : U h <-> T.OpenAt i h := carries sourceH.left
      exact Iff.mp carryH sourceH.right
    ledger_sound := by
      intro h sourceH
      have carryH : U h <-> T.OpenAt i h := carries sourceH.left
      exact Iff.mp carryH sourceH.right
  }

theorem BHistPublicOpenTree_semantic_name_certificate (T : BHistIndexedOpenCarrier)
    {U : BHist -> Prop} (tree : BHistPublicOpenTree T U)
    (source : exists h : BHist, UnaryHistory h ∧ U h) :
    SemanticNameCert (fun h : BHist => UnaryHistory h ∧ U h) (fun h : BHist => U h)
      (fun h : BHist => Nonempty (BHistPublicOpenTree T U) ∧ U h)
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
        have transport :
            U h <-> U k :=
          BHistPublicOpenTree_classifier_transport T tree sourceH.left classified.right.left
            classified.right.right
        exact And.intro classified.right.left (Iff.mp transport sourceH.right)
    }
    pattern_sound := by
      intro h sourceH
      exact sourceH.right
    ledger_sound := by
      intro h sourceH
      exact And.intro (Nonempty.intro tree) sourceH.right
  }

end BEDC.Derived.TopologyUp
