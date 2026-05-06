import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.RootSystemUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def RootSystemFiniteSupportCarrier
    (support : ProbeBundle BHist)
    (Vector Nonzero : BHist -> Prop)
    (h : BHist) : Prop :=
  InBundle h support ∧ Vector h ∧ Nonzero h

theorem RootSystemFiniteSupportCarrier_project_rows
    {support : ProbeBundle BHist} {Vector Nonzero : BHist -> Prop} {h : BHist} :
    RootSystemFiniteSupportCarrier support Vector Nonzero h ->
      InBundle h support ∧ Vector h ∧ Nonzero h := by
  intro carrierH
  exact And.intro carrierH.left (And.intro carrierH.right.left carrierH.right.right)

def RootSystemFiniteSupportClassifier
    (support : ProbeBundle BHist)
    (VectorClassifier : BHist -> BHist -> Prop)
    (h k : BHist) : Prop :=
  InBundle h support ∧ InBundle k support ∧ hsame h k ∧ VectorClassifier h k

theorem RootSystemFiniteSupportCarrier_nonzero_rows {support : ProbeBundle BHist}
    {Vector Nonzero : BHist -> Prop}
    (vector_unary : forall {h : BHist}, Vector h -> UnaryHistory h) {h : BHist} :
    RootSystemFiniteSupportCarrier support Vector Nonzero h ->
      InBundle h support ∧ Vector h ∧ Nonzero h ∧ UnaryHistory h := by
  intro carrier
  exact And.intro carrier.left
    (And.intro carrier.right.left
      (And.intro carrier.right.right (vector_unary carrier.right.left)))

theorem RootSystemFiniteSupportCarrier_classifier_transport
    {support : ProbeBundle BHist}
    {Vector Nonzero : BHist -> Prop}
    {VectorClassifier : BHist -> BHist -> Prop}
    (vector_transport :
      forall {h k : BHist}, Vector h -> VectorClassifier h k -> Vector k)
    (nonzero_transport : forall {h k : BHist}, Nonzero h -> hsame h k -> Nonzero k)
    {h k : BHist} :
    RootSystemFiniteSupportCarrier support Vector Nonzero h ->
      RootSystemFiniteSupportClassifier support VectorClassifier h k ->
        RootSystemFiniteSupportCarrier support Vector Nonzero k := by
  intro carrierH classifiedHK
  exact And.intro classifiedHK.right.left
    (And.intro
      (vector_transport carrierH.right.left classifiedHK.right.right.right)
      (nonzero_transport carrierH.right.right classifiedHK.right.right.left))

theorem RootSystemReflectionClosure_result_unary
    {support : ProbeBundle BHist} {Vector Nonzero : BHist -> Prop}
    {alpha beta reflected : BHist}
    (vector_unary : forall {h : BHist}, Vector h -> UnaryHistory h) :
    RootSystemFiniteSupportCarrier support Vector Nonzero alpha ->
      RootSystemFiniteSupportCarrier support Vector Nonzero beta ->
        Cont alpha beta reflected -> UnaryHistory reflected := by
  intro alphaCarrier betaCarrier reflectionRoute
  exact unary_cont_closed (vector_unary alphaCarrier.right.left)
    (vector_unary betaCarrier.right.left) reflectionRoute

theorem RootSystemCartanLedger_cont_transport
    {IntCarrier : BHist -> Prop} {IntClassifier : BHist -> BHist -> Prop}
    (int_transport : forall {h k : BHist}, IntCarrier h -> IntClassifier h k -> IntCarrier k)
    (int_hsame : forall {h k : BHist}, hsame h k -> IntClassifier h k)
    {raw transported route : BHist} :
    IntCarrier raw -> Cont raw route transported -> hsame route BHist.Empty ->
      IntCarrier transported ∧ IntClassifier raw transported := by
  intro rawCarrier rawRoute routeEmpty
  cases routeEmpty
  cases rawRoute
  have rawClassified : IntClassifier raw raw :=
    int_hsame rfl
  exact And.intro (int_transport rawCarrier rawClassified) rawClassified

theorem RootSystemFiniteSupport_semanticNameCert
    {support : ProbeBundle BHist}
    {Vector Nonzero : BHist -> Prop}
    {VectorClassifier : BHist -> BHist -> Prop}
    (rootWitness :
      exists h : BHist, RootSystemFiniteSupportCarrier support Vector Nonzero h)
    (vector_refl : forall {h : BHist}, Vector h -> VectorClassifier h h)
    (vector_symm :
      forall {h k : BHist}, VectorClassifier h k -> VectorClassifier k h)
    (vector_trans :
      forall {h k r : BHist}, VectorClassifier h k -> VectorClassifier k r ->
        VectorClassifier h r)
    (vector_transport :
      forall {h k : BHist}, Vector h -> VectorClassifier h k -> Vector k)
    (nonzero_transport : forall {h k : BHist}, Nonzero h -> hsame h k -> Nonzero k) :
    SemanticNameCert
      (RootSystemFiniteSupportCarrier support Vector Nonzero)
      (RootSystemFiniteSupportCarrier support Vector Nonzero)
      (RootSystemFiniteSupportCarrier support Vector Nonzero)
      (RootSystemFiniteSupportClassifier support VectorClassifier) := by
  refine {
    core := ?core
    pattern_sound := ?pattern_sound
    ledger_sound := ?ledger_sound
  }
  · refine {
      carrier_inhabited := rootWitness
      equiv_refl := ?equiv_refl
      equiv_symm := ?equiv_symm
      equiv_trans := ?equiv_trans
      carrier_respects_equiv := ?carrier_respects_equiv
    }
    · intro h carrierH
      exact And.intro carrierH.left
        (And.intro carrierH.left (And.intro rfl (vector_refl carrierH.right.left)))
    · intro h k classifiedHK
      exact And.intro classifiedHK.right.left
        (And.intro classifiedHK.left
          (And.intro
            (hsame_symm classifiedHK.right.right.left)
            (vector_symm classifiedHK.right.right.right)))
    · intro h k r classifiedHK classifiedKR
      have sameHR : hsame h r :=
        hsame_trans classifiedHK.right.right.left classifiedKR.right.right.left
      have vectorHR : VectorClassifier h r :=
        vector_trans classifiedHK.right.right.right classifiedKR.right.right.right
      exact And.intro classifiedHK.left
        (And.intro classifiedKR.right.left (And.intro sameHR vectorHR))
    · intro h k classifiedHK carrierH
      exact And.intro classifiedHK.right.left
        (And.intro
          (vector_transport carrierH.right.left classifiedHK.right.right.right)
          (nonzero_transport carrierH.right.right classifiedHK.right.right.left))
  · intro h source
    exact source
  · intro h source
    exact source

end BEDC.Derived.RootSystemUp
