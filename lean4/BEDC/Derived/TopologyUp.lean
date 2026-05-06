import BEDC.Derived.TopologyUp.Core
import BEDC.Derived.TopologyUp.Singleton
import BEDC.FKernel.Cont
import BEDC.FKernel.Bundle
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.TopologyUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

inductive BHistRootPublicOpenTree (T : BHistIndexedOpenCarrier) :
    T.OpenIx -> (BHist -> Prop) -> Prop where
  | singleton : forall {i : T.OpenIx} {U : BHist -> Prop},
      BHistCarriesOpen T i U -> BHistRootPublicOpenTree T i U
  | meet : forall {i j : T.OpenIx} {U V : BHist -> Prop},
      BHistRootPublicOpenTree T i U -> BHistRootPublicOpenTree T j V ->
        BHistRootPublicOpenTree T (T.meet i j) (fun h : BHist => U h ∧ V h)

theorem BHistPublicOpenTree_root_classifier_transport (T : BHistIndexedOpenCarrier)
    {i : T.OpenIx} {U : BHist -> Prop} :
    BHistRootPublicOpenTree T i U ->
      forall {x y : BHist}, UnaryHistory x -> UnaryHistory y -> hsame x y -> (U x <-> U y) := by
  intro tree
  induction tree with
  | singleton carries =>
      intro x y unaryX unaryY sameXY
      exact BHistCarriesOpen_classifier_transport T carries unaryX unaryY sameXY
  | meet leftTree rightTree leftTransport rightTransport =>
      intro x y unaryX unaryY sameXY
      have leftStable : _ :=
        leftTransport unaryX unaryY sameXY
      have rightStable : _ :=
        rightTransport unaryX unaryY sameXY
      constructor
      · intro rootX
        exact And.intro (Iff.mp leftStable rootX.left) (Iff.mp rightStable rootX.right)
      · intro rootY
        exact And.intro (Iff.mpr leftStable rootY.left) (Iff.mpr rightStable rootY.right)

inductive BHistLedgerPublicOpenTree (T : BHistIndexedOpenCarrier) :
    T.OpenIx -> (BHist -> Prop) -> BHist -> Prop where
  | base {i : T.OpenIx} {U : BHist -> Prop} {ledger : BHist} :
      BHistCarriesOpen T i U -> BHistLedgerPublicOpenTree T i U ledger
  | meet {i j : T.OpenIx} {U V : BHist -> Prop} {leftLedger rightLedger : BHist} :
      BHistLedgerPublicOpenTree T i U leftLedger ->
        BHistLedgerPublicOpenTree T j V rightLedger ->
          BHistLedgerPublicOpenTree T (T.meet i j) (fun x : BHist => U x ∧ V x)
            (BHist.e0 (append leftLedger rightLedger))
  | union {A : Type} {u : T.OpenIx} {ι : A -> T.OpenIx} {U : A -> BHist -> Prop}
      {ledger : A -> BHist} :
      (forall a : A, BHistLedgerPublicOpenTree T (ι a) (U a) (ledger a)) ->
        (forall {x : BHist}, UnaryHistory x ->
          (T.OpenAt u x <-> exists a : A, T.OpenAt (ι a) x)) ->
          BHistLedgerPublicOpenTree T u (fun x : BHist => exists a : A, U a x)
            (BHist.e1 BHist.Empty)
  | bottom (boundary : BHistIndexedBoundaryOpen T) :
      BHistLedgerPublicOpenTree T boundary.bottom (fun _ : BHist => False)
        (BHist.e0 BHist.Empty)
  | top (boundary : BHistIndexedBoundaryOpen T) :
      BHistLedgerPublicOpenTree T boundary.top (fun _ : BHist => True)
        (BHist.e1 BHist.Empty)

theorem BHistPublicOpenTree_carries_open (T : BHistIndexedOpenCarrier)
    {i : T.OpenIx} {U : BHist -> Prop} {ledger : BHist} :
    BHistLedgerPublicOpenTree T i U ledger -> BHistCarriesOpen T i U := by
  intro tree
  induction tree with
  | base carries =>
      exact carries
  | meet leftTree rightTree leftCarries rightCarries =>
      exact (BHistIndexedOpen_finite_intersection_closure T leftCarries rightCarries).left
  | union subtrees unionLaw subtreeCarries =>
      exact (BHistIndexedOpen_arbitrary_union_closure T unionLaw subtreeCarries).left
  | bottom boundary =>
      exact (BHistIndexedOpen_boundary_closure T boundary).left
  | top boundary =>
      exact (BHistIndexedOpen_boundary_closure T boundary).right.left

theorem BHistPublicOpenTree_unary_membership_transport (T : BHistIndexedOpenCarrier)
    {i : T.OpenIx} {U : BHist -> Prop} {ledger x y : BHist} :
    BHistLedgerPublicOpenTree T i U ledger -> UnaryHistory x -> UnaryHistory y -> hsame x y ->
      (U x <-> U y) := by
  intro tree unaryX unaryY sameXY
  exact BHistCarriesOpen_classifier_transport T
    (BHistPublicOpenTree_carries_open T tree) unaryX unaryY sameXY

end BEDC.Derived.TopologyUp
