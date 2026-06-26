import BEDC.Algebra.Spine.Arithmetic
import BEDC.Algebra.FiniteFold
import BEDC.Algebra.FinPerm
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Algebra.Spine.OrderSetType

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.NameCert
open BEDC.Algebra.Rel
open BEDC.Algebra.FiniteFold
open BEDC.Algebra.FinPerm
open BEDC.Algebra.Spine.FiniteData
open BEDC.Algebra.Spine.Arithmetic

abbrev Hist := BHist

structure RelLedger (X : CarrierUp) (R : Hist -> Hist -> Prop) where
  left_closed : forall {x y : Hist}, R x y -> X.carrier x
  right_closed : forall {x y : Hist}, R x y -> X.carrier y
  respects_same :
    forall {x x' y y' : Hist},
      X.same x x' -> X.same y y' -> R x y -> R x' y'

structure NameCertRel (X : CarrierUp) (R : Hist -> Hist -> Prop) where
  carrier_cert : NameCert X.carrier X.same
  ledger : RelLedger X R

structure RelIface (X : CarrierUp) where
  R : Hist -> Hist -> Prop
  R_carrier_left : forall {x y : Hist}, R x y -> X.carrier x
  R_carrier_right : forall {x y : Hist}, R x y -> X.carrier y
  R_congr :
    forall {x x' y y' : Hist},
      X.same x x' -> X.same y y' -> R x y -> R x' y'
  ledger : RelLedger X R
  cert : NameCertRel X R

namespace RelIface

theorem ledger_left {X : CarrierUp} (I : RelIface X) {x y : Hist} :
    I.R x y -> X.carrier x :=
  I.ledger.left_closed

theorem ledger_right {X : CarrierUp} (I : RelIface X) {x y : Hist} :
    I.R x y -> X.carrier y :=
  I.ledger.right_closed

theorem ledger_congr {X : CarrierUp} (I : RelIface X)
    {x x' y y' : Hist} :
    X.same x x' -> X.same y y' -> I.R x y -> I.R x' y' :=
  I.ledger.respects_same

end RelIface

structure PreorderUp (X : CarrierUp) extends RelIface X where
  refl : forall {x : Hist}, X.carrier x -> R x x
  trans : forall {x y z : Hist}, R x y -> R y z -> R x z

structure PosetUp (X : CarrierUp) extends PreorderUp X where
  antisymm : forall {x y : Hist}, R x y -> R y x -> X.same x y

inductive CompareData (R : Hist -> Hist -> Prop) (x y : Hist) : Type where
  | left : R x y -> CompareData R x y
  | right : R y x -> CompareData R x y

structure TotalOrderUp (X : CarrierUp) extends PosetUp X where
  compare :
    forall {x y : Hist}, X.carrier x -> X.carrier y ->
      CompareData R x y

structure LowerBound (P : PosetUp X) (m x y : Hist) : Prop where
  left : P.R m x
  right : P.R m y

structure UpperBound (P : PosetUp X) (j x y : Hist) : Prop where
  left : P.R x j
  right : P.R y j

structure MeetSpec (P : PosetUp X) (m x y : Hist) : Prop where
  lower : LowerBound P m x y
  greatest : forall {z : Hist}, LowerBound P z x y -> P.R z m

structure JoinSpec (P : PosetUp X) (j x y : Hist) : Prop where
  upper : UpperBound P j x y
  least : forall {z : Hist}, UpperBound P z x y -> P.R j z

structure LatticeUp (X : CarrierUp) extends PosetUp X where
  meet : Hist -> Hist -> Hist
  join : Hist -> Hist -> Hist
  meet_spec :
    forall {x y : Hist}, X.carrier x -> X.carrier y ->
      MeetSpec toPosetUp (meet x y) x y
  join_spec :
    forall {x y : Hist}, X.carrier x -> X.carrier y ->
      JoinSpec toPosetUp (join x y) x y

def UnaryPrefixRel : Hist -> Hist -> Prop :=
  NatLE

private theorem cont_unary_prefix_succ {x y tail : Hist} :
    Unary tail -> ContR x tail y -> ContR (.e1 x) tail (.e1 y) := by
  intro tailUnary hcont
  induction tail generalizing x y with
  | Empty =>
      cases hcont
      rfl
  | e0 tail ih =>
      cases tailUnary
  | e1 tail ih =>
      cases hcont
      have inner :
          ContR (.e1 x) tail (.e1 (append x tail)) :=
        ih tailUnary (cont_intro rfl)
      exact congrArg BHist.e1 inner

private def unary_prefix_compare_data :
    forall {x y : Hist}, Unary x -> Unary y -> CompareData UnaryPrefixRel x y
  | .Empty, y, hx, hy =>
      CompareData.left ⟨hx, hy, y, hy, cont_left_unit y⟩
  | .e0 x, y, hx, _hy =>
      False.elim (unary_no_zero_extension hx)
  | .e1 x, .Empty, hx, hy =>
      CompareData.right ⟨hy, hx, .e1 x, hx, cont_left_unit (.e1 x)⟩
  | .e1 x, .e0 y, _hx, hy =>
      False.elim (unary_no_zero_extension hy)
  | .e1 x, .e1 y, hx, hy =>
      match unary_prefix_compare_data
          (x := x) (y := y) (unary_e1_inversion hx) (unary_e1_inversion hy) with
      | CompareData.left leftXY =>
          CompareData.left (by
            cases leftXY.right.right with
            | intro tail tailData =>
                exact ⟨hx, hy, tail, tailData.left,
                  cont_unary_prefix_succ tailData.left tailData.right⟩)
      | CompareData.right rightYX =>
          CompareData.right (by
            cases rightYX.right.right with
            | intro tail tailData =>
                exact ⟨hy, hx, tail, tailData.left,
                  cont_unary_prefix_succ tailData.left tailData.right⟩)

private theorem natle_carrier_left {x y : Hist} :
    UnaryPrefixRel x y -> NatCarrierUp.carrier x := by
  intro hxy
  exact hxy.left

private theorem natle_carrier_right {x y : Hist} :
    UnaryPrefixRel x y -> NatCarrierUp.carrier y := by
  intro hxy
  exact hxy.right.left

private theorem unary_hsame_transport {x y : Hist} :
    hsame x y -> Unary x -> Unary y := by
  intro sameXY ux
  cases sameXY
  exact ux

private theorem natle_congr {x x' y y' : Hist} :
    NatCarrierUp.same x x' -> NatCarrierUp.same y y' ->
      UnaryPrefixRel x y -> UnaryPrefixRel x' y' := by
  intro sameXX sameYY hxy
  cases hxy.right.right with
  | intro tail tailData =>
      exact ⟨sameXX.right.left, sameYY.right.left, tail, tailData.left,
        cont_hsame_transport
          sameXX.right.right (hsame_refl tail) sameYY.right.right tailData.right⟩

def UnaryPrefixLedger : RelLedger NatCarrierUp UnaryPrefixRel where
  left_closed := by
    intro x y hxy
    exact natle_carrier_left hxy
  right_closed := by
    intro x y hxy
    exact natle_carrier_right hxy
  respects_same := by
    intro x x' y y' sameXX sameYY hxy
    exact natle_congr sameXX sameYY hxy

def UnaryPrefixNameCertRel : NameCertRel NatCarrierUp UnaryPrefixRel where
  carrier_cert := NatFinDataIface.cert
  ledger := UnaryPrefixLedger

def UnaryPrefixIface : RelIface NatCarrierUp where
  R := UnaryPrefixRel
  R_carrier_left := by
    intro x y hxy
    exact natle_carrier_left hxy
  R_carrier_right := by
    intro x y hxy
    exact natle_carrier_right hxy
  R_congr := by
    intro x x' y y' sameXX sameYY hxy
    exact natle_congr sameXX sameYY hxy
  ledger := UnaryPrefixLedger
  cert := UnaryPrefixNameCertRel

def UnaryPrefixPreorder : PreorderUp NatCarrierUp where
  toRelIface := UnaryPrefixIface
  refl := by
    intro x hx
    exact natle_refl hx
  trans := by
    intro x y z hxy hyz
    exact natle_trans hxy hyz

def UnaryPrefixPoset : PosetUp NatCarrierUp where
  toPreorderUp := UnaryPrefixPreorder
  antisymm := by
    intro x y hxy hyx
    exact natle_antisymm hxy hyx

def UnaryTotalOrder : TotalOrderUp NatCarrierUp where
  toPosetUp := UnaryPrefixPoset
  compare := by
    intro x y hx hy
    exact unary_prefix_compare_data hx hy

structure SetLedger (E : CarrierUp) (mem : Hist -> Prop) where
  mem_closed : forall {x : Hist}, mem x -> E.carrier x
  respects_same : forall {x y : Hist}, E.same x y -> mem x -> mem y
  witness : exists x : Hist, E.carrier x

structure NameCertSet (E : CarrierUp) (mem : Hist -> Prop) where
  carrier_cert : NameCert E.carrier E.same
  ledger : SetLedger E mem

structure SetLikeUp (E : CarrierUp) : Type where
  mem : Hist -> Prop
  mem_carrier : forall {x : Hist}, mem x -> E.carrier x
  mem_congr : forall {x y : Hist}, E.same x y -> mem x -> mem y
  ledger : SetLedger E mem
  cert : NameCertSet E mem

def SubsetUp {E : CarrierUp} (S T : SetLikeUp E) : Prop :=
  forall x : Hist, E.carrier x -> S.mem x -> T.mem x

def SetLikeSame {E : CarrierUp} (S T : SetLikeUp E) : Prop :=
  SubsetUp S T /\ SubsetUp T S

theorem subset_refl {E : CarrierUp} (S : SetLikeUp E) :
    SubsetUp S S := by
  intro x hx hmem
  exact hmem

theorem subset_trans {E : CarrierUp} {S T U : SetLikeUp E} :
    SubsetUp S T -> SubsetUp T U -> SubsetUp S U := by
  intro st tu x hx hmem
  exact tu x hx (st x hx hmem)

theorem setlike_same_refl {E : CarrierUp} (S : SetLikeUp E) :
    SetLikeSame S S :=
  ⟨subset_refl S, subset_refl S⟩

theorem setlike_same_symm {E : CarrierUp} {S T : SetLikeUp E} :
    SetLikeSame S T -> SetLikeSame T S := by
  intro sameST
  exact ⟨sameST.right, sameST.left⟩

theorem setlike_same_trans {E : CarrierUp} {S T U : SetLikeUp E} :
    SetLikeSame S T -> SetLikeSame T U -> SetLikeSame S U := by
  intro sameST sameTU
  exact ⟨subset_trans sameST.left sameTU.left,
    subset_trans sameTU.right sameST.right⟩

def setlike_same_equiv (E : CarrierUp) :
    RelEquiv (SetLikeUp E) where
  rel := SetLikeSame
  refl := by
    intro S
    exact setlike_same_refl S
  symm := by
    intro S T sameST
    exact setlike_same_symm sameST
  trans := by
    intro S T U sameST sameTU
    exact setlike_same_trans sameST sameTU

def FullSetLike (E : CarrierUp) (I : FinDataIface E) : SetLikeUp E where
  mem := E.carrier
  mem_carrier := by
    intro x hx
    exact hx
  mem_congr := by
    intro x y sameXY _hx
    exact E.same_right_carrier sameXY
  ledger := {
    mem_closed := by
      intro x hx
      exact hx
    respects_same := by
      intro x y sameXY _hx
      exact E.same_right_carrier sameXY
    witness := I.ledger.carrier_witness
  }
  cert := {
    carrier_cert := I.cert
    ledger := {
      mem_closed := by
        intro x hx
        exact hx
      respects_same := by
        intro x y sameXY _hx
        exact E.same_right_carrier sameXY
      witness := I.ledger.carrier_witness
    }
  }

inductive ListMemUp (E : CarrierUp) : Hist -> ListSpine E -> Prop where
  | head {a : Hist} {ha : E.carrier a} {tail : ListSpine E} :
      ListMemUp E a (ListSpine.cons a ha tail)
  | tail {x a : Hist} {ha : E.carrier a} {tail : ListSpine E} :
      ListMemUp E x tail -> ListMemUp E x (ListSpine.cons a ha tail)

inductive NoDupRel (E : CarrierUp) : ListSpine E -> Prop where
  | nil : NoDupRel E ListSpine.nil
  | cons {a : Hist} {ha : E.carrier a} {tail : ListSpine E} :
      (forall {x : Hist}, ListMemUp E x tail -> E.same a x -> False) ->
      NoDupRel E tail ->
        NoDupRel E (ListSpine.cons a ha tail)

structure FinSetUp (E : CarrierUp) where
  elems : Hist
  spine : ListSpine E
  elems_code : hsame elems (ListSpine.code spine)
  list_carrier : ListCarrier E elems
  nodup_rel : NoDupRel E spine
  mem : Hist -> Prop
  mem_iff_list_mem :
    forall {x : Hist}, E.carrier x ->
      (mem x -> ListMemUp E x spine) /\ (ListMemUp E x spine -> mem x)

def EmptyFinSetUp (E : CarrierUp) : FinSetUp E where
  elems := ListSpine.code (A := E) ListSpine.nil
  spine := ListSpine.nil
  elems_code := hsame_refl (ListSpine.code (A := E) ListSpine.nil)
  list_carrier := ⟨ListSpine.nil, hsame_refl (ListSpine.code (A := E) ListSpine.nil)⟩
  nodup_rel := NoDupRel.nil
  mem := fun _x => False
  mem_iff_list_mem := by
    intro x hx
    exact ⟨fun h => False.elim h, fun listed => by cases listed⟩

structure FiberEquiv (A B : CarrierUp) where
  forward : forall {x : Hist}, A.carrier x -> B.carrier x
  backward : forall {x : Hist}, B.carrier x -> A.carrier x
  forward_respects_same :
    forall {x y : Hist}, A.same x y -> B.same x y
  backward_respects_same :
    forall {x y : Hist}, B.same x y -> A.same x y

def FiberEquiv.refl (A : CarrierUp) : FiberEquiv A A where
  forward := by
    intro x hx
    exact hx
  backward := by
    intro x hx
    exact hx
  forward_respects_same := by
    intro x y hxy
    exact hxy
  backward_respects_same := by
    intro x y hxy
    exact hxy

def FiberEquiv.symm {A B : CarrierUp} (e : FiberEquiv A B) :
    FiberEquiv B A where
  forward := e.backward
  backward := e.forward
  forward_respects_same := e.backward_respects_same
  backward_respects_same := e.forward_respects_same

def FiberEquiv.trans {A B C : CarrierUp}
    (ab : FiberEquiv A B) (bc : FiberEquiv B C) :
    FiberEquiv A C where
  forward := by
    intro x hx
    exact bc.forward (ab.forward hx)
  backward := by
    intro x hx
    exact ab.backward (bc.backward hx)
  forward_respects_same := by
    intro x y hxy
    exact bc.forward_respects_same (ab.forward_respects_same hxy)
  backward_respects_same := by
    intro x y hxy
    exact ab.backward_respects_same (bc.backward_respects_same hxy)

structure TypeFamilyLedger (index : CarrierUp) (fiber : Hist -> CarrierUp) where
  index_witness : exists i : Hist, index.carrier i
  fiber_witness : forall {i : Hist}, index.carrier i -> exists x : Hist, (fiber i).carrier x
  stable :
    forall {i j : Hist}, index.same i j -> FiberEquiv (fiber i) (fiber j)

structure TypeLikeUp : Type where
  index : CarrierUp
  fiber : Hist -> CarrierUp
  fiber_congr : forall {i j : Hist}, index.same i j -> FiberEquiv (fiber i) (fiber j)
  ledger : TypeFamilyLedger index fiber

def ConstantTypeLikeUp (index fiber : CarrierUp)
    (indexIface : FinDataIface index) (fiberIface : FinDataIface fiber) :
    TypeLikeUp where
  index := index
  fiber := fun _i => fiber
  fiber_congr := by
    intro i j _sameIJ
    exact FiberEquiv.refl fiber
  ledger := {
    index_witness := indexIface.ledger.carrier_witness
    fiber_witness := by
      intro i hi
      exact fiberIface.ledger.carrier_witness
    stable := by
      intro i j _sameIJ
      exact FiberEquiv.refl fiber
  }

structure OrderSetTypeSpineRows where
  relIface : RelIface NatCarrierUp
  preorder : PreorderUp NatCarrierUp
  poset : PosetUp NatCarrierUp
  totalOrder : TotalOrderUp NatCarrierUp
  setSameEquiv :
    RelEquiv (SetLikeUp NatCarrierUp)
  emptyFinSet : FinSetUp NatCarrierUp
  constantType : TypeLikeUp
  identityPerm : FinPerm 0

def orderSetTypeSpineRows : OrderSetTypeSpineRows where
  relIface := UnaryPrefixIface
  preorder := UnaryPrefixPreorder
  poset := UnaryPrefixPoset
  totalOrder := UnaryTotalOrder
  setSameEquiv := setlike_same_equiv NatCarrierUp
  emptyFinSet := EmptyFinSetUp NatCarrierUp
  constantType := ConstantTypeLikeUp NatCarrierUp NatCarrierUp
    NatFinDataIface NatFinDataIface
  identityPerm := FinPerm.identity 0

end BEDC.Algebra.Spine.OrderSetType
