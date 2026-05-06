import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.BundleUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def BundleLocalTrivCocyclePkg
    (base total projection fibre ledger : BHist) (trivializations transitions : ProbeBundle BHist) :
    Prop :=
  UnaryHistory base ∧ UnaryHistory total ∧ UnaryHistory projection ∧ UnaryHistory fibre ∧
    UnaryHistory ledger ∧ Cont base total projection ∧ Cont projection fibre ledger ∧
      (∀ {row : BHist}, InBundle row trivializations -> UnaryHistory row) ∧
        (∀ {row : BHist}, InBundle row transitions -> UnaryHistory row)

theorem BundleLocalTrivPkg_transition_cocycle_ledger_closure
    {base total projection fibre ledger tij tjk tik composed displayed : BHist}
    {trivializations transitions : ProbeBundle BHist} :
    BundleLocalTrivCocyclePkg base total projection fibre ledger trivializations transitions ->
      InBundle tij transitions ->
      InBundle tjk transitions ->
      InBundle tik transitions ->
      Cont tij tjk composed ->
      Cont tik ledger displayed ->
        hsame displayed (append tik ledger) ∧ UnaryHistory composed ∧ UnaryHistory displayed := by
  intro package tijInTransitions tjkInTransitions tikInTransitions composedReadback displayedReadback
  have ledgerUnary : UnaryHistory ledger :=
    package.right.right.right.right.left
  have transitionRowsUnary :
      ∀ {row : BHist}, InBundle row transitions -> UnaryHistory row :=
    package.right.right.right.right.right.right.right.right
  have tijUnary : UnaryHistory tij :=
    transitionRowsUnary tijInTransitions
  have tjkUnary : UnaryHistory tjk :=
    transitionRowsUnary tjkInTransitions
  have tikUnary : UnaryHistory tik :=
    transitionRowsUnary tikInTransitions
  have composedUnary : UnaryHistory composed :=
    unary_cont_closed tijUnary tjkUnary composedReadback
  have displayedUnary : UnaryHistory displayed :=
    unary_cont_closed tikUnary ledgerUnary displayedReadback
  exact And.intro displayedReadback (And.intro composedUnary displayedUnary)

def BundleLocalTrivSemanticPkg
    (base total projection fiber ledger : BHist)
    (trivRows transitionRows : ProbeBundle BHist) : Prop :=
  Cont base total ledger ∧ InBundle projection trivRows ∧ InBundle fiber transitionRows

theorem BundleLocalTrivPkg_semantic_name_certificate :
    SemanticNameCert
      (fun ledger : BHist =>
        ∃ base total projection fiber : BHist, ∃ trivRows transitionRows : ProbeBundle BHist,
          BundleLocalTrivSemanticPkg base total projection fiber ledger trivRows transitionRows)
      (fun ledger : BHist =>
        ∃ base total projection fiber : BHist, ∃ trivRows transitionRows : ProbeBundle BHist,
          BundleLocalTrivSemanticPkg base total projection fiber ledger trivRows transitionRows)
      (fun ledger : BHist =>
        ∃ base total projection fiber : BHist, ∃ trivRows transitionRows : ProbeBundle BHist,
          BundleLocalTrivSemanticPkg base total projection fiber ledger trivRows transitionRows)
      (fun left right : BHist =>
        (∃ base total projection fiber : BHist, ∃ trivRows transitionRows : ProbeBundle BHist,
          BundleLocalTrivSemanticPkg base total projection fiber left trivRows transitionRows) ∧
        (∃ base total projection fiber : BHist, ∃ trivRows transitionRows : ProbeBundle BHist,
          BundleLocalTrivSemanticPkg base total projection fiber right trivRows transitionRows) ∧
        hsame left right) := by
  let singletonRows : ProbeBundle BHist := ProbeBundle.Bcons BHist.Empty ProbeBundle.Bnil
  let carrier : BHist -> Prop := fun ledger : BHist =>
    ∃ base total projection fiber : BHist, ∃ trivRows transitionRows : ProbeBundle BHist,
      BundleLocalTrivSemanticPkg base total projection fiber ledger trivRows transitionRows
  have emptyPkg : BundleLocalTrivSemanticPkg BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty singletonRows singletonRows := by
    exact And.intro (cont_left_unit BHist.Empty)
      (And.intro (inBundle_cons_self BHist.Empty ProbeBundle.Bnil)
        (inBundle_cons_self BHist.Empty ProbeBundle.Bnil))
  have emptyCarrier : carrier BHist.Empty :=
    Exists.intro BHist.Empty
      (Exists.intro BHist.Empty
        (Exists.intro BHist.Empty
          (Exists.intro BHist.Empty
            (Exists.intro singletonRows (Exists.intro singletonRows emptyPkg)))))
  exact {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty emptyCarrier
      equiv_refl := by
        intro h source
        exact And.intro source (And.intro source (hsame_refl h))
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
        intro h k classified _source
        exact classified.right.left
    }
    pattern_sound := by
      intro _h source
      exact source
    ledger_sound := by
      intro _h source
      exact source
  }

inductive BundleLocalTrivBundle : ProbeBundle BHist -> Prop where
  | bnil : BundleLocalTrivBundle .Bnil
  | bcons {row : BHist} {tail : ProbeBundle BHist} :
      UnaryHistory row -> BundleLocalTrivBundle tail ->
        BundleLocalTrivBundle (.Bcons row tail)

inductive BundleLocalTrivBundleClassifier :
    ProbeBundle BHist -> ProbeBundle BHist -> Prop where
  | bnil : BundleLocalTrivBundleClassifier .Bnil .Bnil
  | bcons {row row' : BHist} {tail tail' : ProbeBundle BHist} :
      hsame row row' -> BundleLocalTrivBundleClassifier tail tail' ->
        BundleLocalTrivBundleClassifier (.Bcons row tail) (.Bcons row' tail')

def BundleLocalTrivComponentPackage
    (base total projection fibre : BHist) (triv : ProbeBundle BHist)
    (transition ledger : BHist) : Prop :=
  UnaryHistory base ∧ UnaryHistory total ∧ UnaryHistory projection ∧ UnaryHistory fibre ∧
    BundleLocalTrivBundle triv ∧ UnaryHistory transition ∧ UnaryHistory ledger ∧
      Cont base total projection ∧ Cont projection fibre transition ∧
        Cont transition ledger total

def BundleLocalTrivClassifier
    (base total projection fibre : BHist) (triv : ProbeBundle BHist)
    (transition ledger base' total' projection' fibre' : BHist) (triv' : ProbeBundle BHist)
    (transition' ledger' : BHist) : Prop :=
  hsame base base' ∧ hsame total total' ∧ hsame projection projection' ∧
    hsame fibre fibre' ∧ BundleLocalTrivBundleClassifier triv triv' ∧
      hsame transition transition' ∧ hsame ledger ledger'

theorem BundleLocalTrivBundle_classifier_transport {triv triv' : ProbeBundle BHist} :
    BundleLocalTrivBundle triv -> BundleLocalTrivBundleClassifier triv triv' ->
      BundleLocalTrivBundle triv' := by
  intro bundle classified
  induction classified with
  | bnil =>
      exact BundleLocalTrivBundle.bnil
  | bcons sameRow sameTail ih =>
      cases bundle with
      | bcons rowUnary tailBundle =>
          exact BundleLocalTrivBundle.bcons (unary_transport rowUnary sameRow)
            (ih tailBundle)

theorem BundleLocalTrivPackage_classifier_transport
    {base total projection fibre transition ledger base' total' projection' fibre' transition'
      ledger' : BHist}
    {triv triv' : ProbeBundle BHist} :
    BundleLocalTrivComponentPackage base total projection fibre triv transition ledger ->
      BundleLocalTrivClassifier base total projection fibre triv transition ledger base' total'
        projection' fibre' triv' transition' ledger' ->
        BundleLocalTrivComponentPackage base' total' projection' fibre' triv' transition' ledger' ∧
          Cont base' total' projection' ∧ Cont projection' fibre' transition' := by
  intro package classified
  have sameBase : hsame base base' := classified.left
  have sameTotal : hsame total total' := classified.right.left
  have sameProjection : hsame projection projection' := classified.right.right.left
  have sameFibre : hsame fibre fibre' := classified.right.right.right.left
  have sameTriv : BundleLocalTrivBundleClassifier triv triv' :=
    classified.right.right.right.right.left
  have sameTransition : hsame transition transition' :=
    classified.right.right.right.right.right.left
  have sameLedger : hsame ledger ledger' :=
    classified.right.right.right.right.right.right
  have baseUnary : UnaryHistory base := package.left
  have totalUnary : UnaryHistory total := package.right.left
  have projectionUnary : UnaryHistory projection := package.right.right.left
  have fibreUnary : UnaryHistory fibre := package.right.right.right.left
  have trivRows : BundleLocalTrivBundle triv := package.right.right.right.right.left
  have transitionUnary : UnaryHistory transition := package.right.right.right.right.right.left
  have ledgerUnary : UnaryHistory ledger := package.right.right.right.right.right.right.left
  have projectionRow : Cont base total projection :=
    package.right.right.right.right.right.right.right.left
  have transitionRow : Cont projection fibre transition :=
    package.right.right.right.right.right.right.right.right.left
  have ledgerRow : Cont transition ledger total :=
    package.right.right.right.right.right.right.right.right.right
  have baseUnary' : UnaryHistory base' := unary_transport baseUnary sameBase
  have totalUnary' : UnaryHistory total' := unary_transport totalUnary sameTotal
  have projectionUnary' : UnaryHistory projection' :=
    unary_transport projectionUnary sameProjection
  have fibreUnary' : UnaryHistory fibre' := unary_transport fibreUnary sameFibre
  have trivRows' : BundleLocalTrivBundle triv' :=
    BundleLocalTrivBundle_classifier_transport trivRows sameTriv
  have transitionUnary' : UnaryHistory transition' :=
    unary_transport transitionUnary sameTransition
  have ledgerUnary' : UnaryHistory ledger' := unary_transport ledgerUnary sameLedger
  have projectionRow' : Cont base' total' projection' := by
    cases sameBase
    cases sameTotal
    cases sameProjection
    exact projectionRow
  have transitionRow' : Cont projection' fibre' transition' := by
    cases sameProjection
    cases sameFibre
    cases sameTransition
    exact transitionRow
  have ledgerRow' : Cont transition' ledger' total' := by
    cases sameTransition
    cases sameLedger
    cases sameTotal
    exact ledgerRow
  have package' :
      BundleLocalTrivComponentPackage base' total' projection' fibre' triv' transition' ledger' :=
    And.intro baseUnary'
      (And.intro totalUnary'
        (And.intro projectionUnary'
          (And.intro fibreUnary'
            (And.intro trivRows'
              (And.intro transitionUnary'
                (And.intro ledgerUnary'
                  (And.intro projectionRow'
                    (And.intro transitionRow' ledgerRow'))))))))
  exact And.intro package' (And.intro projectionRow' transitionRow')

structure BundleLocalTrivPkg (package : BHist) : Type where
  base : BHist
  total : BHist
  projection : BHist
  fibre : BHist
  transition : BHist
  ledger : BHist
  charts : ProbeBundle BHist
  projection_row : hsame projection (append base total)
  package_row : hsame package (append projection fibre)
  transition_row : hsame package (append transition ledger)
  package_unary : UnaryHistory package

def BundleLocalTrivCarrier (package : BHist) : Prop :=
  Nonempty (BundleLocalTrivPkg package)

theorem BundleLocalTrivPkg_trivialization_transition_stability {package package' : BHist} :
    BundleLocalTrivCarrier package → hsame package package' →
      ∃ base total projection fibre transition ledger : BHist,
        ∃ _charts : ProbeBundle BHist,
          BundleLocalTrivCarrier package' ∧ hsame projection (append base total) ∧
            hsame package' (append projection fibre) ∧
              hsame package' (append transition ledger) ∧ UnaryHistory package' := by
  intro carrier samePackage
  cases carrier with
  | intro pkg =>
      have packageProjection : hsame package' (append pkg.projection pkg.fibre) :=
        hsame_trans (hsame_symm samePackage) pkg.package_row
      have packageTransition : hsame package' (append pkg.transition pkg.ledger) :=
        hsame_trans (hsame_symm samePackage) pkg.transition_row
      have packageUnary : UnaryHistory package' :=
        unary_transport pkg.package_unary samePackage
      exact ⟨pkg.base, pkg.total, pkg.projection, pkg.fibre, pkg.transition, pkg.ledger,
        pkg.charts, ⟨Nonempty.intro {
          base := pkg.base
          total := pkg.total
          projection := pkg.projection
          fibre := pkg.fibre
          transition := pkg.transition
          ledger := pkg.ledger
          charts := pkg.charts
          projection_row := pkg.projection_row
          package_row := packageProjection
          transition_row := packageTransition
          package_unary := packageUnary
        }, pkg.projection_row, packageProjection, packageTransition, packageUnary⟩⟩

def BundleLocalTrivTransitionPkg
    (base total projection fibre transition ledger : BHist) (trivs : ProbeBundle BHist) :
    Prop :=
  UnaryHistory base ∧ UnaryHistory total ∧ UnaryHistory projection ∧ UnaryHistory fibre ∧
    UnaryHistory transition ∧ UnaryHistory ledger ∧ Cont base projection total ∧
      Cont total fibre transition ∧ InBundle transition trivs

theorem BundleLocalTrivPkg_transition_stability
    {base total projection fibre transition ledger base' total' projection' fibre' transition'
      ledger' : BHist}
    {trivs : ProbeBundle BHist} :
    BundleLocalTrivTransitionPkg base total projection fibre transition ledger trivs ->
      hsame base base' -> hsame total total' -> hsame projection projection' ->
        hsame fibre fibre' -> hsame transition transition' -> hsame ledger ledger' ->
          BundleLocalTrivTransitionPkg base' total' projection' fibre' transition' ledger' trivs ∧
            hsame transition transition' ∧ UnaryHistory transition' ∧
              InBundle transition' trivs := by
  intro pkg sameBase sameTotal sameProjection sameFibre sameTransition sameLedger
  cases sameBase
  cases sameTotal
  cases sameProjection
  cases sameFibre
  cases sameTransition
  cases sameLedger
  exact And.intro pkg
    (And.intro (hsame_refl transition)
      (And.intro pkg.right.right.right.right.left
        pkg.right.right.right.right.right.right.right.right))

def BundleRowsUnary : ProbeBundle BHist -> Prop
  | .Bnil => True
  | .Bcons row tail => UnaryHistory row ∧ BundleRowsUnary tail

def BundleLocalTrivPackage
    (base total projection fiber : BHist) (trivs transitions : ProbeBundle BHist)
    (ledger : BHist) : Prop :=
  UnaryHistory base ∧ UnaryHistory total ∧ UnaryHistory projection ∧ UnaryHistory fiber ∧
    UnaryHistory ledger ∧ BundleRowsUnary trivs ∧ BundleRowsUnary transitions

theorem BundleLocalTrivPackage_carrier_projection
    {base total projection fiber ledger : BHist} {trivs transitions : ProbeBundle BHist} :
    BundleLocalTrivPackage base total projection fiber trivs transitions ledger ->
      UnaryHistory base ∧ UnaryHistory total ∧ UnaryHistory projection ∧ UnaryHistory fiber ∧
        UnaryHistory ledger ∧ BundleRowsUnary trivs ∧ BundleRowsUnary transitions := by
  intro package
  exact And.intro package.left
    (And.intro package.right.left
      (And.intro package.right.right.left
        (And.intro package.right.right.right.left
          (And.intro package.right.right.right.right.left
            (And.intro package.right.right.right.right.right.left
              package.right.right.right.right.right.right)))))

def BundleLocalTrivPkgRows (base total projection fibre ledger : BHist)
    (triv transitions : ProbeBundle BHist) : ProbeBundle BHist :=
  ProbeBundle.Bcons base
    (ProbeBundle.Bcons total
      (ProbeBundle.Bcons projection
        (ProbeBundle.Bcons fibre
          (bundleAppend triv (ProbeBundle.Bcons ledger transitions)))))

theorem BundleLocalTrivPkg_projection_rows {base total projection fibre ledger row : BHist}
    {triv transitions : ProbeBundle BHist} :
    InBundle row (BundleLocalTrivPkgRows base total projection fibre ledger triv transitions) ->
      row = base ∨ row = total ∨ row = projection ∨ row = fibre ∨ InBundle row triv ∨
        row = ledger ∨ InBundle row transitions := by
  intro member
  cases member with
  | inl sameBase =>
      exact Or.inl sameBase
  | inr memberTotalTail =>
      cases memberTotalTail with
      | inl sameTotal =>
          exact Or.inr (Or.inl sameTotal)
      | inr memberProjectionTail =>
          cases memberProjectionTail with
          | inl sameProjection =>
              exact Or.inr (Or.inr (Or.inl sameProjection))
          | inr memberFibreTail =>
              cases memberFibreTail with
              | inl sameFibre =>
                  exact Or.inr (Or.inr (Or.inr (Or.inl sameFibre)))
              | inr memberTail =>
                  cases Iff.mp inBundle_bundleAppend_iff memberTail with
                  | inl memberTriv =>
                      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl memberTriv))))
                  | inr memberLedgerTail =>
                      cases memberLedgerTail with
                      | inl sameLedger =>
                          exact Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr (Or.inr (Or.inl sameLedger)))))
                      | inr memberTransitions =>
                          exact Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr (Or.inr (Or.inr memberTransitions)))))

theorem BundleLocalTrivPkg_trivialization_scope {base total projection fibre ledger row : BHist}
    {triv transitions : ProbeBundle BHist} :
    InBundle row triv ->
      InBundle row (BundleLocalTrivPkgRows base total projection fibre ledger triv transitions) := by
  intro memberTriv
  exact Or.inr
    (Or.inr
      (Or.inr
        (Or.inr
          (Iff.mpr inBundle_bundleAppend_iff (Or.inl memberTriv)))))

end BEDC.Derived.BundleUp
