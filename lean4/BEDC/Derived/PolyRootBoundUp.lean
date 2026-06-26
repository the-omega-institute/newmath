import BEDC.Derived.FermatWilsonUp
import BEDC.Derived.ZModResidueList

namespace BEDC.Derived.PolyRootBoundUp

open BEDC.Algebra.Rel
open BEDC.FKernel.Hist
open BEDC.Derived.PrimeUp
open BEDC.Derived.ZModUp
open BEDC.Derived.ZModFieldUp
open BEDC.Derived.FermatWilsonUp
open BEDC.Derived.ZModResidueList

variable {A : Type u} {rel : A -> A -> Prop}

namespace RelCommRingTools

theorem add_four_assoc (R : RelCommRing A rel) (a b c d : A) :
    rel (R.add a (R.add (R.add b c) d))
      (R.add (R.add a b) (R.add c d)) := by
  exact R.trans
    (R.add_congr (R.refl a) (R.add_assoc b c d))
    (R.symm (R.add_assoc a b (R.add c d)))

theorem sub_add_cancel_left (R : RelCommRing A rel) (x y : A) :
    rel (R.add y (R.sub x y)) x := by
  exact R.trans
    (R.add_congr (R.refl y) (R.sub_eq_add_neg x y))
    (R.trans
      (R.symm (R.add_assoc y x (R.neg y)))
      (R.trans
        (R.add_congr (R.add_comm y x) (R.refl (R.neg y)))
        (R.trans
          (R.add_assoc x y (R.neg y))
          (R.trans
            (R.add_congr (R.refl x) (R.add_neg y))
            (R.add_zero x)))))

theorem mul_sub_add_decomp (R : RelCommRing A rel) (x y t : A) :
    rel (R.add (R.mul y t) (R.mul (R.sub x y) t)) (R.mul x t) := by
  exact R.trans
    (R.symm (R.right_distrib y (R.sub x y) t))
    (R.mul_congr (sub_add_cancel_left R x y) (R.refl t))

theorem mul_left_comm (R : RelCommRing A rel) (x y z : A) :
    rel (R.mul x (R.mul y z)) (R.mul y (R.mul x z)) := by
  exact R.trans
    (R.symm (R.mul_assoc x y z))
    (R.trans
      (R.mul_congr (R.mul_comm x y) (R.refl z))
      (R.mul_assoc y x z))

theorem horner_difference_step (R : RelCommRing A rel)
    (x y c tailX tailY q : A)
    (tailStep : rel tailX (R.add tailY (R.mul (R.sub x y) q))) :
    rel (R.add c (R.mul x tailX))
      (R.add (R.add c (R.mul y tailY))
        (R.mul (R.sub x y) (R.add tailY (R.mul x q)))) := by
  let f := R.sub x y
  have replaceTail :
      rel (R.mul x tailX) (R.mul x (R.add tailY (R.mul f q))) :=
    R.mul_congr (R.refl x) tailStep
  have distributeX :
      rel (R.mul x (R.add tailY (R.mul f q)))
        (R.add (R.mul x tailY) (R.mul x (R.mul f q))) :=
    R.left_distrib x tailY (R.mul f q)
  have commuteProduct :
      rel (R.mul x (R.mul f q)) (R.mul f (R.mul x q)) :=
    mul_left_comm R x f q
  have splitXTail :
      rel (R.mul x tailY) (R.add (R.mul y tailY) (R.mul f tailY)) :=
    R.symm (mul_sub_add_decomp R x y tailY)
  have inner :
      rel (R.mul x tailX)
        (R.add (R.add (R.mul y tailY) (R.mul f tailY))
          (R.mul f (R.mul x q))) := by
    exact R.trans replaceTail
      (R.trans distributeX
        (R.add_congr splitXTail commuteProduct))
  have outer :
      rel (R.add c (R.mul x tailX))
        (R.add c
          (R.add (R.add (R.mul y tailY) (R.mul f tailY))
            (R.mul f (R.mul x q)))) :=
    R.add_congr (R.refl c) inner
  have regroup :
      rel
        (R.add c
          (R.add (R.add (R.mul y tailY) (R.mul f tailY))
            (R.mul f (R.mul x q))))
        (R.add (R.add c (R.mul y tailY))
          (R.add (R.mul f tailY) (R.mul f (R.mul x q)))) :=
    add_four_assoc R c (R.mul y tailY) (R.mul f tailY) (R.mul f (R.mul x q))
  have collectFactor :
      rel (R.add (R.mul f tailY) (R.mul f (R.mul x q)))
        (R.mul f (R.add tailY (R.mul x q))) :=
    R.symm (R.left_distrib f tailY (R.mul x q))
  exact R.trans outer
    (R.trans regroup
      (R.add_congr (R.refl (R.add c (R.mul y tailY))) collectFactor))

end RelCommRingTools

def zmodRing {p : BHist} (prime : NatPrime p) :
    RelCommRing (ZMod p) zmodEq :=
  zmodRelCommRing prime

def zmodSub {p : BHist} (prime : NatPrime p) (x y : ZMod p) : ZMod p :=
  (zmodRing prime).sub x y

def polyEval {p : BHist} (prime : NatPrime p) :
    List (ZMod p) -> ZMod p -> ZMod p
  | [], _x =>
      (zmodRing prime).zero
  | c :: cs, x =>
      (zmodRing prime).add c ((zmodRing prime).mul x (polyEval prime cs x))

def polyDeflateData {p : BHist} (prime : NatPrime p) (r : ZMod p) :
    List (ZMod p) -> Bool × List (ZMod p)
  | [] => (false, [])
  | _c :: cs =>
      match polyDeflateData prime r cs with
      | (false, out) => (true, out)
      | (true, out) => (true, polyEval prime cs r :: out)

def polyDeflateAt {p : BHist} (prime : NatPrime p) (r : ZMod p)
    (coeffs : List (ZMod p)) : List (ZMod p) :=
  (polyDeflateData prime r coeffs).snd

theorem polyDeflateAt_singleton {p : BHist} (prime : NatPrime p)
    (r c : ZMod p) :
    polyDeflateAt prime r [c] = [] := by
  rfl

theorem polyDeflateData_nonempty {p : BHist} (prime : NatPrime p)
    (r c : ZMod p) (cs : List (ZMod p)) :
    (polyDeflateData prime r (c :: cs)).fst = true := by
  cases h : polyDeflateData prime r cs with
  | mk seen out =>
      change
        (match polyDeflateData prime r cs with
          | (false, out) => (true, out)
          | (true, out) => (true, polyEval prime cs r :: out)).fst = true
      rw [h]
      cases seen <;> rfl

theorem polyDeflateAt_cons_cons {p : BHist} (prime : NatPrime p)
    (r c cnext : ZMod p) (cs : List (ZMod p)) :
    polyDeflateAt prime r (c :: cnext :: cs) =
      polyEval prime (cnext :: cs) r ::
        polyDeflateAt prime r (cnext :: cs) := by
  have tailSeen := polyDeflateData_nonempty prime r cnext cs
  unfold polyDeflateAt
  change
    (match polyDeflateData prime r (cnext :: cs) with
      | (false, out) => (true, out)
      | (true, out) =>
          (true, polyEval prime (cnext :: cs) r :: out)).snd =
      polyEval prime (cnext :: cs) r ::
        (polyDeflateData prime r (cnext :: cs)).snd
  cases h : polyDeflateData prime r (cnext :: cs) with
  | mk seen out =>
      cases seen with
      | false =>
          rw [h] at tailSeen
          cases tailSeen
      | true =>
          rfl

def PolyRoot {p : BHist} (prime : NatPrime p)
    (coeffs : List (ZMod p)) (x : ZMod p) : Prop :=
  zmodEq (polyEval prime coeffs x) (zmodRing prime).zero

def PolyDegreeExact {p : BHist} (prime : NatPrime p) :
    List (ZMod p) -> Nat -> Prop
  | [], _ => False
  | c :: [], 0 => zmodNonzero c
  | _ :: [], Nat.succ _ => False
  | _ :: _ :: _, 0 => False
  | _ :: cs@(_ :: _), Nat.succ d => PolyDegreeExact prime cs d

theorem polyDegreeExact_constant {p : BHist} (prime : NatPrime p)
    {c : ZMod p} :
    zmodNonzero c -> PolyDegreeExact prime [c] 0 := by
  intro nonzero
  exact nonzero

theorem polyDegreeExact_step {p : BHist} (prime : NatPrime p)
    {c : ZMod p} {cs : List (ZMod p)} {d : Nat} :
    PolyDegreeExact prime cs d ->
      PolyDegreeExact prime (c :: cs) (Nat.succ d) := by
  intro degree
  cases cs with
  | nil =>
      cases d with
      | zero =>
          exact False.elim degree
      | succ dTail =>
          exact False.elim degree
  | cons cnext ctail =>
      exact degree

theorem polyEval_singleton {p : BHist} (prime : NatPrime p)
    (c x : ZMod p) :
    zmodEq (polyEval prime [c] x) c := by
  let R := zmodRing prime
  exact R.trans
    (R.add_congr (R.refl c) (R.mul_zero x))
    (R.add_zero c)

theorem polyEval_nil {p : BHist} (prime : NatPrime p)
    (x : ZMod p) :
    zmodEq (polyEval prime [] x) (zmodRing prime).zero := by
  rfl

theorem zmodSub_zero_imp_eq {p : BHist} (prime : NatPrime p)
    {x y : ZMod p} :
    zmodEq (zmodSub prime x y) (zmodRing prime).zero -> x = y := by
  intro subZero
  let R := zmodRing prime
  have same : zmodEq x y := by
    exact R.trans (R.symm (R.add_zero x))
      (R.trans
        (R.add_congr (R.refl x) (R.symm (R.neg_add y)))
        (R.trans
          (R.symm (R.add_assoc x (R.neg y) y))
          (R.trans
            (R.add_congr subZero (R.refl y))
            (R.zero_add y))))
  exact zmod_ext same

theorem zmodSub_nonzero_of_ne {p : BHist} (prime : NatPrime p)
    {x y : ZMod p} :
    (x = y -> False) -> zmodNonzero (zmodSub prime x y) := by
  intro notEq subZero
  exact notEq (zmodSub_zero_imp_eq prime subZero)

theorem polyFactor_eval {p : BHist} (prime : NatPrime p)
    (r x : ZMod p) :
    ∀ coeffs : List (ZMod p),
      zmodEq (polyEval prime coeffs x)
        ((zmodRing prime).add (polyEval prime coeffs r)
          ((zmodRing prime).mul (zmodSub prime x r)
            (polyEval prime (polyDeflateAt prime r coeffs) x)))
  | [] => by
      let R := zmodRing prime
      exact R.symm
        (R.trans
          (R.add_congr (R.refl R.zero) (R.mul_zero (zmodSub prime x r)))
          (R.add_zero R.zero))
  | c :: [] => by
      let R := zmodRing prime
      have rightToC :
          zmodEq
            (R.add (polyEval prime [c] r)
              (R.mul (zmodSub prime x r)
                (polyEval prime (polyDeflateAt prime r [c]) x)))
            c := by
        exact R.trans
          (R.add_congr (polyEval_singleton prime c r)
            (R.mul_zero (zmodSub prime x r)))
          (R.add_zero c)
      exact R.trans (polyEval_singleton prime c x) (R.symm rightToC)
  | c :: cnext :: cs => by
      let R := zmodRing prime
      rw [polyDeflateAt_cons_cons prime r c cnext cs]
      change zmodEq
        (R.add c (R.mul x (polyEval prime (cnext :: cs) x)))
        (R.add (R.add c (R.mul r (polyEval prime (cnext :: cs) r)))
          (R.mul (zmodSub prime x r)
            (R.add (polyEval prime (cnext :: cs) r)
              (R.mul x (polyEval prime (polyDeflateAt prime r (cnext :: cs)) x)))))
      exact RelCommRingTools.horner_difference_step R x r c
        (polyEval prime (cnext :: cs) x)
        (polyEval prime (cnext :: cs) r)
        (polyEval prime (polyDeflateAt prime r (cnext :: cs)) x)
        (polyFactor_eval prime r x (cnext :: cs))

theorem polyDeflateAt_root_of_distinct_root {p : BHist} (prime : NatPrime p)
    {coeffs : List (ZMod p)} {r x : ZMod p} :
    zmodNonzero (zmodSub prime x r) ->
      PolyRoot prime coeffs r ->
        PolyRoot prime coeffs x ->
          PolyRoot prime (polyDeflateAt prime r coeffs) x := by
  intro factorNonzero rootR rootX
  let R := zmodRing prime
  let factor := zmodSub prime x r
  let qValue := polyEval prime (polyDeflateAt prime r coeffs) x
  have factorIdentity :
      zmodEq (polyEval prime coeffs x)
        (R.add (polyEval prime coeffs r) (R.mul factor qValue)) :=
    polyFactor_eval prime r x coeffs
  have rightZero :
      zmodEq (R.add (polyEval prime coeffs r) (R.mul factor qValue)) R.zero :=
    R.trans (R.symm factorIdentity) rootX
  have rightReduce :
      zmodEq (R.add (polyEval prime coeffs r) (R.mul factor qValue))
        (R.mul factor qValue) :=
    R.trans (R.add_congr rootR (R.refl (R.mul factor qValue)))
      (R.zero_add (R.mul factor qValue))
  have productZero : zmodEq (R.mul factor qValue) R.zero :=
    R.trans (R.symm rightReduce) rightZero
  have zeroProduct : zmodEq (R.mul factor R.zero) R.zero :=
    R.mul_zero factor
  have sameProduct : zmodEq (R.mul factor qValue) (R.mul factor R.zero) :=
    R.trans productZero (R.symm zeroProduct)
  exact zmodMul_left_cancel_nonzero prime factorNonzero sameProduct

def polyDeflateAt_degree_exact {p : BHist} (prime : NatPrime p)
    {coeffs : List (ZMod p)} {d : Nat} {r : ZMod p} :
    PolyDegreeExact prime coeffs (Nat.succ d) ->
      PolyDegreeExact prime (polyDeflateAt prime r coeffs) d := by
  intro degree
  cases coeffs with
  | nil =>
      exact False.elim degree
  | cons c cs =>
      cases cs with
      | nil =>
          exact False.elim degree
      | cons cnext ctail =>
          cases d with
          | zero =>
              cases ctail with
              | nil =>
                  exact zmodNonzero_respects
                    (zmodEq_symm (polyEval_singleton prime cnext r)) degree
              | cons cthird crest =>
                  exact False.elim degree
          | succ dTail =>
              rw [polyDeflateAt_cons_cons prime r c cnext ctail]
              exact polyDegreeExact_step prime
                (polyDeflateAt_degree_exact prime degree)

theorem polyRootBound_list {p : BHist} (prime : NatPrime p) :
    ∀ {d : Nat} {coeffs roots : List (ZMod p)},
      PolyDegreeExact prime coeffs d ->
        ListNoDup roots ->
          (∀ x : ZMod p, x ∈ roots -> PolyRoot prime coeffs x) ->
            roots.length <= d
  | 0, coeffs, roots, degree, nodup, allRoots => by
      cases coeffs with
      | nil =>
          exact False.elim degree
      | cons c cs =>
          cases cs with
          | nil =>
              cases roots with
              | nil =>
                  exact Nat.zero_le 0
              | cons x xs =>
                  have rootX : PolyRoot prime [c] x :=
                    allRoots x (List.Mem.head xs)
                  have coeffZero : zmodEq c (zmodRing prime).zero :=
                    (zmodRing prime).trans
                      ((zmodRing prime).symm (polyEval_singleton prime c x))
                      rootX
                  exact False.elim (degree coeffZero)
          | cons cnext ctail =>
              exact False.elim degree
  | Nat.succ d, coeffs, roots, degree, nodup, allRoots => by
      cases roots with
      | nil =>
          exact Nat.zero_le (Nat.succ d)
      | cons r rs =>
          have rootR : PolyRoot prime coeffs r :=
            allRoots r (List.Mem.head rs)
          have tailNodup : ListNoDup rs :=
            listNoDup_tail nodup
          have rNotInTail : r ∈ rs -> False :=
            listNoDup_head_not_mem nodup
          have deflatedDegree :
              PolyDegreeExact prime (polyDeflateAt prime r coeffs) d :=
            polyDeflateAt_degree_exact prime degree
          have deflatedRoots :
              ∀ x : ZMod p, x ∈ rs ->
                PolyRoot prime (polyDeflateAt prime r coeffs) x := by
            intro x xMem
            have rootX : PolyRoot prime coeffs x :=
              allRoots x (List.Mem.tail r xMem)
            have xNeR : x = r -> False := by
              intro same
              cases same
              exact rNotInTail xMem
            exact polyDeflateAt_root_of_distinct_root prime
              (zmodSub_nonzero_of_ne prime xNeR) rootR rootX
          exact Nat.succ_le_succ
            (polyRootBound_list prime deflatedDegree tailNodup deflatedRoots)

#check polyRootBound_list
#check polyFactor_eval
#check polyDeflateAt_root_of_distinct_root

end BEDC.Derived.PolyRootBoundUp
