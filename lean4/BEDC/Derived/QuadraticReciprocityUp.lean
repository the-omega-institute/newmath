import BEDC.Derived.LegendreUp
import BEDC.Derived.FermatLittleUp
import BEDC.Derived.ZModResidueList

namespace BEDC.Derived.QuadraticReciprocityUp

/-!
二次互反律的 Eisenstein 路线需要三个独立层面：
Gauss 负最小剩余计数、floor-sum 奇偶、以及矩形格点分割。
本文件只登记可由 kernel 直接检查的计算层和结构恒等式。
Gauss 引理、floor-sum 奇偶、Eisenstein floor-sum 与互反律保持为
可计算谓词；缺少平方类分解与 floor 算术桥时不登记成 theorem。
-/

inductive QRSign where
  | pos : QRSign
  | neg : QRSign
deriving DecidableEq

namespace QRSign

def flip : QRSign -> QRSign
  | pos => QRSign.neg
  | neg => QRSign.pos

def mul : QRSign -> QRSign -> QRSign
  | pos, s => s
  | neg, s => flip s

theorem flip_flip (s : QRSign) : flip (flip s) = s := by
  cases s <;> rfl

theorem mul_pos_left (s : QRSign) : mul QRSign.pos s = s := by
  rfl

theorem mul_pos_right (s : QRSign) : mul s QRSign.pos = s := by
  cases s <;> rfl

theorem mul_neg_right (s : QRSign) : mul s QRSign.neg = flip s := by
  cases s <;> rfl

end QRSign

def minusOnePow : Nat -> QRSign
  | 0 => QRSign.pos
  | n + 1 => QRSign.flip (minusOnePow n)

theorem minusOnePow_succ (n : Nat) :
    minusOnePow (n + 1) = QRSign.flip (minusOnePow n) := by
  rfl

inductive NatParity where
  | even : NatParity
  | odd : NatParity
deriving DecidableEq

namespace NatParity

def flip : NatParity -> NatParity
  | even => odd
  | odd => even

theorem flip_flip (p : NatParity) : flip (flip p) = p := by
  cases p <;> rfl

end NatParity

def natParity : Nat -> NatParity
  | 0 => NatParity.even
  | n + 1 => NatParity.flip (natParity n)

def sameParity (m n : Nat) : Prop :=
  natParity m = natParity n

def sameParityBool (m n : Nat) : Bool :=
  natParity m == natParity n

def signOfParity : NatParity -> QRSign
  | NatParity.even => QRSign.pos
  | NatParity.odd => QRSign.neg

theorem minusOnePow_eq_signOfParity :
    ∀ n : Nat, minusOnePow n = signOfParity (natParity n)
  | 0 => by
      rfl
  | n + 1 => by
      change QRSign.flip (minusOnePow n) =
        signOfParity (NatParity.flip (natParity n))
      rw [minusOnePow_eq_signOfParity n]
      cases natParity n <;> rfl

theorem minusOnePow_sameParity {m n : Nat} :
    sameParity m n -> minusOnePow m = minusOnePow n := by
  intro parity
  rw [minusOnePow_eq_signOfParity m, minusOnePow_eq_signOfParity n, parity]

theorem QRSign_mul_flip_left (s t : QRSign) :
    QRSign.mul (QRSign.flip s) t = QRSign.flip (QRSign.mul s t) := by
  cases s <;> cases t <;> rfl

theorem minusOnePow_add :
    ∀ m n : Nat,
      QRSign.mul (minusOnePow m) (minusOnePow n) = minusOnePow (m + n)
  | 0, n => by
      change minusOnePow n = minusOnePow (0 + n)
      rw [Nat.zero_add]
  | m + 1, n => by
      change QRSign.mul (QRSign.flip (minusOnePow m)) (minusOnePow n) =
        minusOnePow (Nat.succ m + n)
      rw [QRSign_mul_flip_left, minusOnePow_add m n, Nat.succ_add]
      rfl

def halfIndex (p : Nat) : Nat :=
  (p - 1) / 2

def oneToAux : Nat -> Nat -> List Nat
  | 0, _start => []
  | n + 1, start => start :: oneToAux n (start + 1)

def oneTo (n : Nat) : List Nat :=
  oneToAux n 1

theorem oneToAux_length :
    ∀ n start : Nat, (oneToAux n start).length = n
  | 0, _start => by
      rfl
  | n + 1, start => by
      change Nat.succ (oneToAux n (start + 1)).length = Nat.succ n
      rw [oneToAux_length n (start + 1)]

theorem oneTo_length (n : Nat) :
    (oneTo n).length = n := by
  unfold oneTo
  exact oneToAux_length n 1

def halfList (p : Nat) : List Nat :=
  oneTo (halfIndex p)

theorem halfList_length (p : Nat) :
    (halfList p).length = halfIndex p := by
  unfold halfList
  exact oneTo_length (halfIndex p)

theorem listMap_length {A : Type u} {B : Type v} (f : A -> B) :
    ∀ xs : List A, (List.map f xs).length = xs.length
  | [] => by
      rfl
  | _x :: xs => by
      change Nat.succ (List.map f xs).length = Nat.succ xs.length
      rw [listMap_length f xs]

theorem listAppend_length {A : Type u} :
    ∀ xs ys : List A, (xs ++ ys).length = xs.length + ys.length
  | [], ys => by
      change ys.length = 0 + ys.length
      rw [Nat.zero_add]
  | _x :: xs, ys => by
      change Nat.succ (xs ++ ys).length =
        Nat.succ xs.length + ys.length
      rw [Nat.succ_add]
      rw [listAppend_length xs ys]

def listSumNat : List Nat -> Nat
  | [] => 0
  | x :: xs => x + listSumNat xs

theorem listSumNat_append :
    ∀ xs ys : List Nat,
      listSumNat (xs ++ ys) = listSumNat xs + listSumNat ys
  | [], ys => by
      change listSumNat ys = 0 + listSumNat ys
      rw [Nat.zero_add]
  | x :: xs, ys => by
      change x + listSumNat (xs ++ ys) =
        (x + listSumNat xs) + listSumNat ys
      rw [listSumNat_append xs ys]
      rw [Nat.add_assoc]

def sumMapNat (f : Nat -> Nat) (xs : List Nat) : Nat :=
  listSumNat (xs.map f)

theorem sumMapNat_append (f : Nat -> Nat) (xs ys : List Nat) :
    sumMapNat f (xs ++ ys) = sumMapNat f xs + sumMapNat f ys := by
  induction xs with
  | nil =>
      change sumMapNat f ys = 0 + sumMapNat f ys
      rw [Nat.zero_add]
  | cons x xs ih =>
      change f x + sumMapNat f (xs ++ ys) =
        (f x + sumMapNat f xs) + sumMapNat f ys
      rw [ih]
      rw [Nat.add_assoc]

def listCountBool {A : Type u} (test : A -> Bool) : List A -> Nat
  | [] => 0
  | x :: xs => (if test x then 1 else 0) + listCountBool test xs

theorem listCountBool_append {A : Type u} (test : A -> Bool) :
    ∀ xs ys : List A,
      listCountBool test (xs ++ ys) =
        listCountBool test xs + listCountBool test ys
  | [], ys => by
      change listCountBool test ys = 0 + listCountBool test ys
      rw [Nat.zero_add]
  | x :: xs, ys => by
      change (if test x then 1 else 0) + listCountBool test (xs ++ ys) =
        ((if test x then 1 else 0) + listCountBool test xs) +
          listCountBool test ys
      rw [listCountBool_append test xs ys]
      rw [Nat.add_assoc]

def listCountEq {A : Type u} [DecidableEq A] (target : A) : List A -> Nat
  | [] => 0
  | x :: xs =>
      (if x = target then 1 else 0) + listCountEq target xs

theorem listCountEq_append {A : Type u} [DecidableEq A] (target : A) :
    ∀ xs ys : List A,
      listCountEq target (xs ++ ys) =
        listCountEq target xs + listCountEq target ys
  | [], ys => by
      change listCountEq target ys = 0 + listCountEq target ys
      rw [Nat.zero_add]
  | x :: xs, ys => by
      change (if x = target then 1 else 0) + listCountEq target (xs ++ ys) =
        ((if x = target then 1 else 0) + listCountEq target xs) +
          listCountEq target ys
      rw [listCountEq_append target xs ys]
      rw [Nat.add_assoc]

structure SignedResidue where
  sign : QRSign
  value : Nat
deriving DecidableEq

def residueOverHalf (p r : Nat) : Bool :=
  if p / 2 < r then true else false

def leastResidue (a p k : Nat) : Nat :=
  (k * a) % p

def leastAbsResidueSigned (a p k : Nat) : SignedResidue :=
  let r := leastResidue a p k
  if p / 2 < r then
    { sign := QRSign.neg, value := p - r }
  else
    { sign := QRSign.pos, value := r }

def signedHalfList (p : Nat) : List SignedResidue :=
  (halfList p).map (fun k => { sign := QRSign.pos, value := k }) ++
    (halfList p).map (fun k => { sign := QRSign.neg, value := k })

theorem signedHalfList_length (p : Nat) :
    (signedHalfList p).length = halfIndex p + halfIndex p := by
  unfold signedHalfList
  rw [listAppend_length, listMap_length, listMap_length,
    halfList_length]

def leastAbsResidues (a p : Nat) : List SignedResidue :=
  (halfList p).map (leastAbsResidueSigned a p)

theorem leastAbsResidues_length (a p : Nat) :
    (leastAbsResidues a p).length = halfIndex p := by
  unfold leastAbsResidues
  rw [listMap_length, halfList_length]

def countMatchOn {A : Type u} [DecidableEq A]
    (domain xs ys : List A) : Prop :=
  ∀ z : A, z ∈ domain -> listCountEq z xs = listCountEq z ys

def countMatchOnCheck {A : Type u} [DecidableEq A]
    (domain xs ys : List A) : Bool :=
  domain.all (fun z => listCountEq z xs == listCountEq z ys)

def leastAbsResidues_perm_halfList (a p : Nat) : Bool :=
  countMatchOnCheck (signedHalfList p) (leastAbsResidues a p) (signedHalfList p)

def gaussNegativeAt (a p k : Nat) : Bool :=
  residueOverHalf p (leastResidue a p k)

def gaussNegCount (a p : Nat) : Nat :=
  listCountBool (gaussNegativeAt a p) (halfList p)

theorem gaussNegCount_append_halfList (a p q : Nat) :
    listCountBool (gaussNegativeAt a p) (halfList p ++ halfList q) =
      gaussNegCount a p +
        listCountBool (gaussNegativeAt a p) (halfList q) := by
  unfold gaussNegCount
  exact listCountBool_append (gaussNegativeAt a p) (halfList p) (halfList q)

def floorTerm (a p k : Nat) : Nat :=
  (k * a) / p

def floorSum (a p : Nat) : Nat :=
  sumMapNat (floorTerm a p) (halfList p)

theorem floorSum_append_halfList (a p q : Nat) :
    sumMapNat (floorTerm a p) (halfList p ++ halfList q) =
      floorSum a p + sumMapNat (floorTerm a p) (halfList q) := by
  unfold floorSum
  exact sumMapNat_append (floorTerm a p) (halfList p) (halfList q)

def NegCountParityEqFloorSum (a p : Nat) : Prop :=
  sameParityBool (gaussNegCount a p) (floorSum a p) = true

def NegCountParityEqFloorSumEq (a p : Nat) : Prop :=
  sameParity (gaussNegCount a p) (floorSum a p)

def negCountParityCheck (a p : Nat) : Bool :=
  sameParityBool (gaussNegCount a p) (floorSum a p)

def pairGrid : List Nat -> List Nat -> List (Nat × Nat)
  | [], _ys => []
  | x :: xs, ys => ys.map (fun y => (x, y)) ++ pairGrid xs ys

theorem pairGrid_length :
    ∀ xs ys : List Nat, (pairGrid xs ys).length = xs.length * ys.length
  | [], ys => by
      change 0 = 0 * ys.length
      rw [Nat.zero_mul]
  | _x :: xs, ys => by
      change (List.map (fun y => (_x, y)) ys ++ pairGrid xs ys).length =
        Nat.succ xs.length * ys.length
      rw [listAppend_length, listMap_length, pairGrid_length xs ys,
        Nat.succ_mul]
      rw [Nat.add_comm]

def eisensteinGrid (p q : Nat) : List (Nat × Nat) :=
  pairGrid (halfList p) (halfList q)

theorem EisensteinFloorSum_grid_cardinality (p q : Nat) :
    (eisensteinGrid p q).length = halfIndex p * halfIndex q := by
  unfold eisensteinGrid
  rw [pairGrid_length, halfList_length, halfList_length]

def EisensteinFloorSumBool (p q : Nat) : Bool :=
  floorSum q p + floorSum p q == halfIndex p * halfIndex q

def EisensteinFloorSum (p q : Nat) : Prop :=
  EisensteinFloorSumBool p q = true

def EisensteinFloorSumEq (p q : Nat) : Prop :=
  floorSum q p + floorSum p q = halfIndex p * halfIndex q

def eisenstein_floor_sum (p q : Nat) : Bool :=
  EisensteinFloorSumBool p q

def GaussLemmaShapeBool (a p : Nat) (symbol : QRSign) : Bool :=
  symbol == minusOnePow (gaussNegCount a p)

def GaussLemmaShape (a p : Nat) (symbol : QRSign) : Prop :=
  GaussLemmaShapeBool a p symbol = true

def GaussLemmaShapeEq (a p : Nat) (symbol : QRSign) : Prop :=
  symbol = minusOnePow (gaussNegCount a p)

def gaussLemmaCheck (a p : Nat) (symbol : QRSign) : Bool :=
  GaussLemmaShapeBool a p symbol

def QRFormulaBool (p q : Nat) (pq qp : QRSign) : Bool :=
  QRSign.mul pq qp == minusOnePow (halfIndex p * halfIndex q)

def QRFormula (p q : Nat) (pq qp : QRSign) : Prop :=
  QRFormulaBool p q pq qp = true

def QRFormulaEq (p q : Nat) (pq qp : QRSign) : Prop :=
  QRSign.mul pq qp = minusOnePow (halfIndex p * halfIndex q)

def quadraticReciprocityCheck (p q : Nat) (pq qp : QRSign) : Bool :=
  QRFormulaBool p q pq qp

theorem quadraticReciprocityFormula_from_gauss_eisenstein
    {p q : Nat} {pq qp : QRSign} :
    GaussLemmaShapeEq p q pq ->
      GaussLemmaShapeEq q p qp ->
        NegCountParityEqFloorSumEq p q ->
          NegCountParityEqFloorSumEq q p ->
            EisensteinFloorSumEq p q ->
              QRFormulaEq p q pq qp := by
  intro gaussPQ gaussQP parityPQ parityQP eisenstein
  unfold QRFormulaEq
  unfold GaussLemmaShapeEq at gaussPQ
  unfold GaussLemmaShapeEq at gaussQP
  rw [gaussPQ, gaussQP]
  rw [minusOnePow_sameParity parityPQ]
  rw [minusOnePow_sameParity parityQP]
  rw [minusOnePow_add]
  unfold EisensteinFloorSumEq at eisenstein
  have ordered :
      floorSum p q + floorSum q p = halfIndex p * halfIndex q := by
    rw [Nat.add_comm (floorSum p q) (floorSum q p)]
    exact eisenstein
  rw [ordered]

end BEDC.Derived.QuadraticReciprocityUp
