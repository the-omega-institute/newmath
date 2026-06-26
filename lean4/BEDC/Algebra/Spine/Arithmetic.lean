import BEDC.Algebra.Spine.FiniteData
import BEDC.Derived.NatUp.NatAdd
import BEDC.Derived.PrimeUp.NatMulComm
import BEDC.Derived.PrimeUp.NatMulTransport
import BEDC.Derived.PrimeUp.DividesClosure
import BEDC.Derived.RationalUp

namespace BEDC.Algebra.Spine.Arithmetic

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Algebra.Rel
open BEDC.Algebra.Spine.FiniteData

abbrev Unary : Hist -> Prop :=
  UnaryHistory

def NatCarrier (h : Hist) : Prop :=
  Unary h

def NatSame (h k : Hist) : Prop :=
  NatCarrier h /\ NatCarrier k /\ hsame h k

def NatZero : Hist :=
  emp

def NatOne : Hist :=
  Eone emp

def NatSucc (h : Hist) : Hist :=
  Eone h

theorem unary_zero : Unary NatZero := by
  exact unary_empty

theorem unary_succ {h : Hist} :
    Unary h -> Unary (NatSucc h) := by
  intro uh
  exact unary_e1_closed uh

theorem unary_induction {P : Hist -> Prop} :
    P NatZero ->
      (forall h : Hist, Unary h -> P h -> P (NatSucc h)) ->
      forall h : Hist, Unary h -> P h := by
  intro base step h uh
  exact unary_history_induction base step h uh

theorem unary_no_zero_head {h t : Hist} :
    Unary h -> hsame h (Ezero t) -> False := by
  intro uh same
  exact unary_history_hsame_zero_absurd uh same

def nat_same_equiv : RelEquiv { h : Hist // NatCarrier h } where
  rel x y := NatSame x.1 y.1
  refl := by
    intro x
    exact ⟨x.2, x.2, hsame_refl x.1⟩
  symm := by
    intro x y sameXY
    exact ⟨sameXY.right.left, sameXY.left, hsame_symm sameXY.right.right⟩
  trans := by
    intro x y z sameXY sameYZ
    exact ⟨sameXY.left, sameYZ.right.left,
      hsame_trans sameXY.right.right sameYZ.right.right⟩

def NatCarrierUp : CarrierUp where
  carrier := NatCarrier
  same := NatSame
  same_equiv := nat_same_equiv
  same_left_carrier := by
    intro h k sameHK
    exact sameHK.left
  same_right_carrier := by
    intro h k sameHK
    exact sameHK.right.left
  same_equiv_sound := by
    intro h k _hh _hk sameHK
    exact sameHK
  same_equiv_complete := by
    intro h k _hh _hk sameHK
    exact sameHK

def NatFinDataIface : FinDataIface NatCarrierUp :=
  carrier_fin_data_iface NatCarrierUp NatZero unary_zero

abbrev AddRel : Hist -> Hist -> Hist -> Prop :=
  BEDC.Derived.NatUp.NatAdd

theorem add_closure {h k r : Hist} :
    Unary h -> Unary k -> ContR h k r -> Unary r := by
  intro uh uk cont
  exact BEDC.Derived.NatUp.NatAdd_result_unary ⟨uh, uk, cont⟩

theorem add_deterministic {h k r r' : Hist} :
    AddRel h k r -> AddRel h k r' -> hsame r r' := by
  intro left right
  exact BEDC.Derived.NatUp.NatAdd_functional left right

theorem add_zero_left {h r : Hist} :
    Unary h -> AddRel NatZero h r -> hsame r h := by
  intro _uh add
  exact cont_left_unit_result add.right.right

theorem add_zero_right {h r : Hist} :
    Unary h -> AddRel h NatZero r -> hsame r h := by
  intro _uh add
  exact cont_deterministic add.right.right (cont_right_unit h)

theorem add_assoc {a b c ab bc abc abc' : Hist} :
    AddRel a b ab -> AddRel b c bc -> AddRel ab c abc ->
      AddRel a bc abc' -> hsame abc abc' := by
  intro addAB addBC addABC addABC'
  exact BEDC.Derived.NatUp.NatAdd_assoc_hsame addAB addBC addABC addABC'

theorem add_comm {h k r r' : Hist} :
    AddRel h k r -> AddRel k h r' -> hsame r r' := by
  intro left right
  exact BEDC.Derived.NatUp.NatAdd_comm_hsame left right

theorem add_cancel_left {h k k' r r' : Hist} :
    AddRel h k r -> AddRel h k' r' -> hsame r r' -> hsame k k' := by
  intro left right sameResult
  exact cont_left_cancel left.right.right
    (cont_result_hsame_transport right.right.right (hsame_symm sameResult))

abbrev NatMul : Hist -> Hist -> Hist -> Prop :=
  BEDC.Derived.PrimeUp.NatMul

theorem natmul_total {d q : Hist} :
    Unary d -> Unary q -> exists n : Hist, Unary n /\ NatMul d q n := by
  intro hd hq
  exact BEDC.Derived.PrimeUp.NatMul_total hd hq

theorem natmul_closure {d q n : Hist} :
    Unary d -> NatMul d q n -> Unary n := by
  intro hd mul
  exact BEDC.Derived.PrimeUp.NatMul_result_unary hd mul

theorem natmul_deterministic {d q n m : Hist} :
    Unary d -> NatMul d q n -> NatMul d q m -> hsame n m := by
  intro hd left right
  exact BEDC.Derived.PrimeUp.NatMul_functional hd left right

theorem natmul_one_left {q n : Hist} :
    Unary q -> NatMul NatOne q n -> hsame n q := by
  intro hq mul
  exact BEDC.Derived.PrimeUp.NatMul_unit_left_hsame hq mul

theorem natmul_one_right {d n : Hist} :
    NatMul d NatOne n -> hsame n d := by
  intro mul
  exact BEDC.Derived.PrimeUp.NatMul_unit_right_hsame mul

theorem natmul_comm {d q n m : Hist} :
    Unary d -> Unary q -> NatMul d q n -> NatMul q d m -> hsame n m := by
  intro hd hq left right
  exact BEDC.Derived.PrimeUp.NatMul_comm_hsame hd hq left right

theorem natmul_assoc {a b c ab left bc right : Hist} :
    Unary a -> Unary b -> Unary c -> NatMul a b ab -> NatMul ab c left ->
      NatMul b c bc -> NatMul a bc right -> hsame left right := by
  intro ha hb hc mulAB mulLeft mulBC mulRight
  exact BEDC.Derived.PrimeUp.NatMul_assoc_hsame
    ha hb hc mulAB mulLeft mulBC mulRight

theorem natmul_right_distrib {a b c ab left ac bc right : Hist} :
    Unary a -> Unary b -> Unary c -> AddRel a b ab -> NatMul ab c left ->
      NatMul a c ac -> NatMul b c bc -> AddRel ac bc right -> hsame left right := by
  intro _ha _hb _hc addAB mulLeft mulAC mulBC addRight
  have derived : AddRel ac bc left :=
    BEDC.Derived.PrimeUp.NatMul_add_right_distrib addAB mulLeft mulAC mulBC
  exact add_deterministic derived addRight

theorem natmul_left_distrib {a b c bc left ab ac right : Hist} :
    Unary a -> Unary b -> Unary c -> AddRel b c bc -> NatMul a bc left ->
      NatMul a b ab -> NatMul a c ac -> AddRel ab ac right -> hsame left right := by
  intro ha hb hc addBC mulLeft mulAB mulAC addRight
  have hbc : Unary bc :=
    BEDC.Derived.NatUp.NatAdd_result_unary addBC
  cases natmul_total hbc ha with
  | intro bca bcaData =>
      cases natmul_total hb ha with
      | intro ba baData =>
          cases natmul_total hc ha with
          | intro ca caData =>
              have addBACABCA : AddRel ba ca bca :=
                BEDC.Derived.PrimeUp.NatMul_add_right_distrib
                  addBC bcaData.right baData.right caData.right
              have sameABBA : hsame ab ba :=
                natmul_comm ha hb mulAB baData.right
              have sameACCA : hsame ac ca :=
                natmul_comm ha hc mulAC caData.right
              have addABACBCA : AddRel ab ac bca := by
                exact ⟨
                  BEDC.Derived.PrimeUp.NatMul_result_unary ha mulAB,
                  BEDC.Derived.PrimeUp.NatMul_result_unary ha mulAC,
                  cont_hsame_transport
                    (hsame_symm sameABBA) (hsame_symm sameACCA) (hsame_refl bca)
                    addBACABCA.right.right⟩
              have sameBCARight : hsame bca right :=
                add_deterministic addABACBCA addRight
              exact hsame_trans (natmul_comm ha hbc mulLeft bcaData.right) sameBCARight

structure NatMulDistributivityRows where
  left_distrib :
    forall {a b c bc left ab ac right : Hist},
      Unary a -> Unary b -> Unary c -> AddRel b c bc -> NatMul a bc left ->
        NatMul a b ab -> NatMul a c ac -> AddRel ab ac right -> hsame left right
  right_distrib :
    forall {a b c ab left ac bc right : Hist},
      Unary a -> Unary b -> Unary c -> AddRel a b ab -> NatMul ab c left ->
        NatMul a c ac -> NatMul b c bc -> AddRel ac bc right -> hsame left right

def natmulDistributivityRows : NatMulDistributivityRows where
  left_distrib := by
    intro a b c bc left ab ac right ha hb hc addBC mulLeft mulAB mulAC addRight
    exact natmul_left_distrib ha hb hc addBC mulLeft mulAB mulAC addRight
  right_distrib := by
    intro a b c ab left ac bc right ha hb hc addAB mulLeft mulAC mulBC addRight
    exact natmul_right_distrib ha hb hc addAB mulLeft mulAC mulBC addRight

def NatLE (h k : Hist) : Prop :=
  Unary h /\ Unary k /\ exists t : Hist, Unary t /\ ContR h t k

def NatLT (h k : Hist) : Prop :=
  NatLE h k /\ exists t : Hist, Unary t /\ (hsame t NatZero -> False) /\ ContR h t k

theorem natle_refl {h : Hist} :
    Unary h -> NatLE h h := by
  intro uh
  exact ⟨uh, uh, NatZero, unary_zero, cont_right_unit h⟩

theorem natle_trans {h k l : Hist} :
    NatLE h k -> NatLE k l -> NatLE h l := by
  intro hk kl
  cases hk.right.right with
  | intro leftTail leftData =>
      cases kl.right.right with
      | intro rightTail rightData =>
          have joinedUnary : Unary (append leftTail rightTail) :=
            unary_append_closed leftData.left rightData.left
          have joinedCont : ContR h (append leftTail rightTail) l := by
            cases leftData.right
            cases rightData.right
            exact cont_intro (append_assoc h leftTail rightTail)
          exact ⟨hk.left, kl.right.left, append leftTail rightTail, joinedUnary, joinedCont⟩

theorem natle_antisymm {h k : Hist} :
    NatLE h k -> NatLE k h -> NatSame h k := by
  intro hk kh
  cases hk.right.right with
  | intro leftTail leftData =>
      cases kh.right.right with
      | intro rightTail rightData =>
          have sameHK : hsame h k := by
            cases leftTail with
            | Empty =>
                exact hsame_symm
                  (cont_deterministic leftData.right (cont_right_unit h))
            | e0 tail =>
                exact False.elim (unary_no_zero_extension leftData.left)
            | e1 tail =>
                cases rightTail with
                | Empty =>
                    exact cont_deterministic rightData.right (cont_right_unit k)
                | e0 rtail =>
                    exact False.elim (unary_no_zero_extension rightData.left)
                | e1 rtail =>
                    have leftStrict : BEDC.Derived.NatUp.NatUnaryStrictPrefix h k :=
                      ⟨Eone tail, leftData.left, (fun empty => by cases empty), leftData.right⟩
                    have rightStrict : BEDC.Derived.NatUp.NatUnaryStrictPrefix k h :=
                      ⟨Eone rtail, rightData.left, (fun empty => by cases empty), rightData.right⟩
                    exact False.elim
                      (BEDC.Derived.NatUp.NatUnaryStrictPrefix_asymm leftStrict rightStrict)
          exact ⟨hk.left, hk.right.left, sameHK⟩

theorem natle_total_data {h k : Hist} :
    Unary h -> Unary k -> NatLE h k \/ NatLE k h := by
  intro uh uk
  have total := BEDC.Derived.NatUp.NatUnaryPrefix_total uh uk
  cases total with
  | inl left =>
      cases left with
      | intro tail data =>
          exact Or.inl ⟨uh, uk, tail, data.left, data.right⟩
  | inr right =>
      cases right with
      | intro tail data =>
          exact Or.inr ⟨uk, uh, tail, data.left, data.right⟩

abbrev IntegerUp :=
  BEDC.Derived.PrimeUp.IntegerUp

structure IntRaw where
  pos : Hist
  neg : Hist
  hpos : Unary pos
  hneg : Unary neg

def IntRaw.toPair (x : IntRaw) : Hist × Hist :=
  (x.pos, x.neg)

def IntRaw.toIntegerUp (x : IntRaw) : IntegerUp :=
  BEDC.Derived.RationalUp.pairToInt x.toPair

theorem intRaw_pair_carrier (x : IntRaw) :
    BEDC.Derived.IntUp.IntPairCarrier x.pos x.neg := by
  exact ⟨x.hpos, x.hneg⟩

def IntSame (x y : IntRaw) : Prop :=
  BEDC.Derived.IntUp.IntPairClassifier x.toPair y.toPair

theorem intsame_refl (x : IntRaw) :
    IntSame x x := by
  exact ⟨intRaw_pair_carrier x, intRaw_pair_carrier x, hsame_refl _⟩

theorem intsame_symm {x y : IntRaw} :
    IntSame x y -> IntSame y x := by
  intro same
  exact BEDC.Derived.IntUp.IntPairClassifier_equivalence_fields.right.right.right.left same

theorem intsame_trans {x y z : IntRaw} :
    IntSame x y -> IntSame y z -> IntSame x z := by
  intro xy yz
  exact BEDC.Derived.IntUp.IntPairClassifier_equivalence_fields.right.right.right.right.left xy yz

def IntAddRel (x y z : IntRaw) : Prop :=
  IntSame z
    { pos := append x.pos y.pos
      neg := append x.neg y.neg
      hpos := unary_append_closed x.hpos y.hpos
      hneg := unary_append_closed x.hneg y.hneg }

def IntNegRel (x z : IntRaw) : Prop :=
  IntSame z
    { pos := x.neg
      neg := x.pos
      hpos := x.hneg
      hneg := x.hpos }

def IntMulRel (x y z : IntRaw) : Prop :=
  IntSame z
    { pos := append
        (BEDC.Derived.IntUp.natMulFn x.pos y.pos)
        (BEDC.Derived.IntUp.natMulFn x.neg y.neg)
      neg := append
        (BEDC.Derived.IntUp.natMulFn x.pos y.neg)
        (BEDC.Derived.IntUp.natMulFn x.neg y.pos)
      hpos := unary_append_closed
        (BEDC.Derived.IntUp.natMulFn_unary x.hpos y.hpos)
        (BEDC.Derived.IntUp.natMulFn_unary x.hneg y.hneg)
      hneg := unary_append_closed
        (BEDC.Derived.IntUp.natMulFn_unary x.hpos y.hneg)
        (BEDC.Derived.IntUp.natMulFn_unary x.hneg y.hpos) }

theorem intAddRel_closed (x y : IntRaw) :
    exists z : IntRaw, IntAddRel x y z := by
  exact ⟨
    { pos := append x.pos y.pos
      neg := append x.neg y.neg
      hpos := unary_append_closed x.hpos y.hpos
      hneg := unary_append_closed x.hneg y.hneg },
    intsame_refl _⟩

theorem intNegRel_closed (x : IntRaw) :
    exists z : IntRaw, IntNegRel x z := by
  exact ⟨
    { pos := x.neg
      neg := x.pos
      hpos := x.hneg
      hneg := x.hpos },
    intsame_refl _⟩

theorem intMulRel_closed (x y : IntRaw) :
    exists z : IntRaw, IntMulRel x y z := by
  exact ⟨
    { pos := append
        (BEDC.Derived.IntUp.natMulFn x.pos y.pos)
        (BEDC.Derived.IntUp.natMulFn x.neg y.neg)
      neg := append
        (BEDC.Derived.IntUp.natMulFn x.pos y.neg)
        (BEDC.Derived.IntUp.natMulFn x.neg y.pos)
      hpos := unary_append_closed
        (BEDC.Derived.IntUp.natMulFn_unary x.hpos y.hpos)
        (BEDC.Derived.IntUp.natMulFn_unary x.hneg y.hneg)
      hneg := unary_append_closed
        (BEDC.Derived.IntUp.natMulFn_unary x.hpos y.hneg)
        (BEDC.Derived.IntUp.natMulFn_unary x.hneg y.hpos) },
    intsame_refl _⟩

structure RatRaw where
  num : IntegerUp
  den : Hist
  den_pos : BEDC.Derived.NatUp.NatUnaryStrictPrefix NatOne den \/ hsame den NatOne
  norm_ledger : Hist

def RatRaw.toRatNum (x : RatRaw) : BEDC.Derived.RationalUp.RatNum :=
  { num := x.num
    den := x.den
    den_pos := x.den_pos }

def RatNormLedger (x y : RatRaw) : Prop :=
  hsame x.norm_ledger y.norm_ledger

def RatSame (x y : RatRaw) : Prop :=
  BEDC.Derived.RationalUp.RatEq x.toRatNum y.toRatNum /\ RatNormLedger x y

theorem ratsame_refl (x : RatRaw) :
    RatSame x x := by
  exact ⟨BEDC.Derived.RationalUp.RatEq_refl x.toRatNum, hsame_refl x.norm_ledger⟩

theorem ratsame_symm {x y : RatRaw} :
    RatSame x y -> RatSame y x := by
  intro same
  exact ⟨BEDC.Derived.RationalUp.RatEq_symm same.left, hsame_symm same.right⟩

theorem ratsame_trans {x y z : RatRaw} :
    RatSame x y -> RatSame y z -> RatSame x z := by
  intro xy yz
  exact ⟨BEDC.Derived.RationalUp.RatEq_trans x.toRatNum y.toRatNum z.toRatNum xy.left yz.left,
    hsame_trans xy.right yz.right⟩

structure ArithmeticSpineRows where
  natCarrier : CarrierUp
  addRel : Hist -> Hist -> Hist -> Prop
  mulRel : Hist -> Hist -> Hist -> Prop
  mulDistrib : NatMulDistributivityRows
  leRel : Hist -> Hist -> Prop
  intSameRel : IntRaw -> IntRaw -> Prop
  ratSameRel : RatRaw -> RatRaw -> Prop

def arithmeticSpineRows : ArithmeticSpineRows where
  natCarrier := NatCarrierUp
  addRel := AddRel
  mulRel := NatMul
  mulDistrib := natmulDistributivityRows
  leRel := NatLE
  intSameRel := IntSame
  ratSameRel := RatSame

end BEDC.Algebra.Spine.Arithmetic
