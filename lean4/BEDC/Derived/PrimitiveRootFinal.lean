import BEDC.Derived.NumberTheoryCapstones

namespace BEDC.Derived.PrimitiveRootFinal

open BEDC.FKernel.Hist
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.PrimeUp
open BEDC.Derived.PrimitiveRootExistence
open BEDC.Derived.PrimitiveRootUp
open BEDC.Derived.ZModFieldUp
open BEDC.Derived.ZModResidueList
open BEDC.Derived.ZModUp

def findBool {alpha : Type u} (b : alpha -> Bool) : List alpha -> Option alpha
  | [] => none
  | x :: xs =>
      if b x then some x else findBool b xs

def findBool_success_of_filter_pos {alpha : Type u} (b : alpha -> Bool) :
    forall xs : List alpha,
      0 < (xs.filter b).length ->
        {x : alpha // findBool b xs = some x /\ b x = true}
  | [], h => by
      exact False.elim (Nat.not_lt_zero 0 h)
  | x :: xs, h => by
      cases hb : b x with
      | false =>
          have filterEq :
              List.filter b (x :: xs) = List.filter b xs :=
            List.filter_cons_of_neg
              (by
                intro htrue
                rw [hb] at htrue
                cases htrue)
          have htail : 0 < (xs.filter b).length := by
            rw [filterEq] at h
            exact h
          let picked := findBool_success_of_filter_pos b xs htail
          exact
            ⟨picked.val,
              And.intro
                (by
                  change
                    (if b x = true then some x else findBool b xs) =
                      some picked.val
                  rw [hb]
                  exact picked.property.left)
                picked.property.right⟩
      | true =>
          exact
            ⟨x,
              And.intro
                (by
                  change
                    (if b x = true then some x else findBool b xs) =
                      some x
                  rw [hb]
                  rfl)
                hb⟩

def natListSum : List Nat -> Nat
  | [] => 0
  | x :: xs => x + natListSum xs

def fiberLengthSum {alpha beta : Type u} [DecidableEq beta]
    (keys : List beta) (key : alpha -> beta) (xs : List alpha) : Nat :=
  natListSum
    (keys.map
      (fun k => (xs.filter (fun x => decide (key x = k))).length))

private theorem natListSum_map_le_each {iota : Type u}
    (ds : List iota) (f g : iota -> Nat) :
    (forall d : iota, d ∈ ds -> f d <= g d) ->
      natListSum (ds.map f) <= natListSum (ds.map g) := by
  intro hle
  induction ds with
  | nil =>
      exact Nat.le_refl 0
  | cons d ds ih =>
      change f d + natListSum (ds.map f) <=
        g d + natListSum (ds.map g)
      exact Nat.add_le_add
        (hle d (List.Mem.head ds))
        (ih (fun e eMem => hle e (List.Mem.tail d eMem)))

private theorem nat_add_left_cancel_pure (a : Nat) :
    forall b c : Nat, a + b = a + c -> b = c
  | b, c, h => by
      induction a with
      | zero =>
          exact (Nat.zero_add b).symm.trans (h.trans (Nat.zero_add c))
      | succ a ih =>
          have hsucc : Nat.succ (a + b) = Nat.succ (a + c) :=
            (Nat.succ_add a b).symm.trans (h.trans (Nat.succ_add a c))
          exact ih (Nat.succ.inj hsucc)

private theorem filter_length_cons_hit_eq_succ
    {alpha beta : Type u} [DecidableEq beta]
    (key : alpha -> beta) (x : alpha) (xs : List alpha) (k : beta) :
    key x = k ->
      ((x :: xs).filter (fun y => decide (key y = k))).length =
        Nat.succ (xs.filter (fun y => decide (key y = k))).length := by
  intro same
  have hit : (fun y : alpha => decide (key y = k)) x = true :=
    decide_eq_true same
  have filterEq :=
    List.filter_cons_of_pos (p := fun y : alpha => decide (key y = k))
      (a := x) (l := xs) hit
  rw [filterEq]
  rfl

private theorem filter_length_cons_miss_eq
    {alpha beta : Type u} [DecidableEq beta]
    (key : alpha -> beta) (x : alpha) (xs : List alpha) (k : beta) :
    (key x = k -> False) ->
      ((x :: xs).filter (fun y => decide (key y = k))).length =
        (xs.filter (fun y => decide (key y = k))).length := by
  intro miss
  have hitFalse : ¬ (fun y : alpha => decide (key y = k)) x = true := by
    intro htrue
    exact miss (of_decide_eq_true htrue)
  have filterEq :=
    List.filter_cons_of_neg (p := fun y : alpha => decide (key y = k))
      (a := x) (l := xs) hitFalse
  rw [filterEq]

theorem eq_each_of_sum_eq_of_le_each {iota : Type u}
    (ds : List iota) (f g : iota -> Nat) :
    (forall d : iota, d ∈ ds -> f d <= g d) ->
      natListSum (ds.map f) = natListSum (ds.map g) ->
        forall d : iota, d ∈ ds -> f d = g d := by
  intro hle hsum
  induction ds with
  | nil =>
      intro d dMem
      cases dMem
  | cons d ds ih =>
      intro target targetMem
      have tailLe :
          natListSum (ds.map f) <= natListSum (ds.map g) :=
        natListSum_map_le_each ds f g
          (fun e eMem => hle e (List.Mem.tail d eMem))
      have headLe : f d <= g d := hle d (List.Mem.head ds)
      have headNotLt : ¬ f d < g d := by
        intro headLt
        have leftLeMid :
            f d + natListSum (ds.map f) <=
              f d + natListSum (ds.map g) :=
          Nat.add_le_add_left tailLe (f d)
        have midLtRight :
            f d + natListSum (ds.map g) <
              g d + natListSum (ds.map g) :=
          Nat.add_lt_add_right headLt (natListSum (ds.map g))
        have leftLtRight :
            f d + natListSum (ds.map f) <
              g d + natListSum (ds.map g) :=
          Nat.lt_of_le_of_lt leftLeMid midLtRight
        have same :
            f d + natListSum (ds.map f) =
              g d + natListSum (ds.map g) := hsum
        rw [same] at leftLtRight
        exact Nat.lt_irrefl _ leftLtRight
      have headEq : f d = g d :=
        Nat.le_antisymm headLe (Nat.not_lt.mp headNotLt)
      cases targetMem with
      | head =>
          exact headEq
      | tail _ tailMem =>
          have tailSum :
              natListSum (ds.map f) = natListSum (ds.map g) := by
            change f d + natListSum (ds.map f) =
              g d + natListSum (ds.map g) at hsum
            rw [headEq] at hsum
            exact nat_add_left_cancel_pure (g d)
              (natListSum (ds.map f)) (natListSum (ds.map g)) hsum
          exact ih
            (fun e eMem => hle e (List.Mem.tail d eMem))
            tailSum target tailMem

private theorem fiberLengthSum_cons_nohit
    {alpha beta : Type u} [DecidableEq beta]
    (keys : List beta) (key : alpha -> beta) (x : alpha) (xs : List alpha) :
    (forall k : beta, k ∈ keys -> key x = k -> False) ->
      fiberLengthSum keys key (x :: xs) = fiberLengthSum keys key xs := by
  intro nohit
  induction keys with
  | nil =>
      rfl
  | cons k ks ih =>
      unfold fiberLengthSum
      change
        ((x :: xs).filter (fun y => decide (key y = k))).length +
            natListSum
              (ks.map
                (fun j => ((x :: xs).filter
                  (fun y => decide (key y = j))).length)) =
          (xs.filter (fun y => decide (key y = k))).length +
            natListSum
              (ks.map
                (fun j => (xs.filter
                  (fun y => decide (key y = j))).length))
      have miss : key x = k -> False :=
        nohit k (List.Mem.head ks)
      have headEq :
          ((x :: xs).filter (fun y => decide (key y = k))).length =
            (xs.filter (fun y => decide (key y = k))).length := by
        by_cases same : key x = k
        · exact False.elim (miss same)
        · exact filter_length_cons_miss_eq key x xs k
            (fun sameHit => same sameHit)
      have tailEq :
          fiberLengthSum ks key (x :: xs) = fiberLengthSum ks key xs :=
        ih (fun j jMem same =>
          nohit j (List.Mem.tail k jMem) same)
      unfold fiberLengthSum at tailEq
      rw [headEq, tailEq]

private theorem fiberLengthSum_cons_hit
    {alpha beta : Type u} [DecidableEq beta]
    (keys : List beta) (key : alpha -> beta) (x : alpha) (xs : List alpha) :
    ListNoDup keys ->
      key x ∈ keys ->
        fiberLengthSum keys key (x :: xs) =
          Nat.succ (fiberLengthSum keys key xs) := by
  intro nodup hit
  induction keys with
  | nil =>
      cases hit
  | cons k ks ih =>
      unfold fiberLengthSum
      change
        ((x :: xs).filter (fun y => decide (key y = k))).length +
            natListSum
              (ks.map
                (fun j => ((x :: xs).filter
                  (fun y => decide (key y = j))).length)) =
          Nat.succ
            ((xs.filter (fun y => decide (key y = k))).length +
              natListSum
                (ks.map
                  (fun j => (xs.filter
                    (fun y => decide (key y = j))).length)))
      by_cases sameHead : key x = k
      · have headEq :
            ((x :: xs).filter (fun y => decide (key y = k))).length =
              Nat.succ
                (xs.filter (fun y => decide (key y = k))).length := by
          exact filter_length_cons_hit_eq_succ key x xs k sameHead
        have tailEq :
            fiberLengthSum ks key (x :: xs) = fiberLengthSum ks key xs :=
          fiberLengthSum_cons_nohit ks key x xs
            (fun j jMem same =>
              listNoDup_head_not_mem nodup
                ((same.symm.trans sameHead) ▸ jMem))
        unfold fiberLengthSum at tailEq
        rw [headEq, tailEq]
        exact Nat.succ_add _ _
      · have tailHit : key x ∈ ks := by
          cases hit with
          | head =>
              exact False.elim (sameHead rfl)
          | tail _ h =>
              exact h
        have headEq :
            ((x :: xs).filter (fun y => decide (key y = k))).length =
              (xs.filter (fun y => decide (key y = k))).length := by
          exact filter_length_cons_miss_eq key x xs k
            (fun sameHit => sameHead sameHit)
        have tailEq :
            fiberLengthSum ks key (x :: xs) =
              Nat.succ (fiberLengthSum ks key xs) :=
          ih (listNoDup_tail nodup) tailHit
        unfold fiberLengthSum at tailEq
        rw [headEq, tailEq]
        exact (Nat.add_succ _ _).symm

private theorem fiberLengthSum_nil
    {alpha beta : Type u} [DecidableEq beta]
    (keys : List beta) (key : alpha -> beta) :
    fiberLengthSum keys key ([] : List alpha) = 0 := by
  induction keys with
  | nil =>
      rfl
  | cons k ks ih =>
      unfold fiberLengthSum
      change
        (([] : List alpha).filter (fun y => decide (key y = k))).length +
            natListSum
              (ks.map
                (fun j => ((([] : List alpha).filter
                  (fun y => decide (key y = j))).length))) =
          0
      change
        0 +
            natListSum
              (ks.map
                (fun j => ((([] : List alpha).filter
                  (fun y => decide (key y = j))).length))) =
          0
      rw [Nat.zero_add]
      exact ih

theorem sum_fiber_lengths_eq_length
    {alpha beta : Type u} [DecidableEq beta]
    (xs : List alpha) (keys : List beta) (key : alpha -> beta) :
    ListNoDup keys ->
      (forall x : alpha, x ∈ xs -> key x ∈ keys) ->
        fiberLengthSum keys key xs = xs.length := by
  intro keysNodup keyMem
  induction xs with
  | nil =>
      exact fiberLengthSum_nil keys key
  | cons x xs ih =>
      change fiberLengthSum keys key (x :: xs) = Nat.succ xs.length
      rw [fiberLengthSum_cons_hit keys key x xs keysNodup
        (keyMem x (List.Mem.head xs))]
      rw [ih (fun y yMem => keyMem y (List.Mem.tail x yMem))]

def topOrderLayer {p : BHist} (prime : NatPrime p) : List (ZMod p) :=
  (nonzeroResidues prime).filter
    (fun x => bhistEqBool (orderOf prime x) (unaryPred p))

theorem primitiveRootSearchFrom_eq_findBool {p : BHist}
    (prime : NatPrime p) :
    forall xs : List (ZMod p),
      primitiveRootSearchFrom prime xs =
        findBool
          (fun x => bhistEqBool (orderOf prime x) (unaryPred p)) xs
  | [] => rfl
  | x :: xs => by
      change
        (if bhistEqBool (orderOf prime x) (unaryPred p) then
          some x
        else primitiveRootSearchFrom prime xs) =
          (if bhistEqBool (orderOf prime x) (unaryPred p) then
            some x
          else
            findBool
              (fun y => bhistEqBool (orderOf prime y) (unaryPred p)) xs)
      cases hit : bhistEqBool (orderOf prime x) (unaryPred p)
      · rw [primitiveRootSearchFrom_eq_findBool prime xs]
      · rfl

def primitiveRootSearchCertificate_of_topOrderLayer_pos {p : BHist}
    (prime : NatPrime p) :
    0 < (topOrderLayer prime).length ->
      PrimitiveRootSearchCertificate prime := by
  intro layerPositive
  let predicate : ZMod p -> Bool :=
    fun x => bhistEqBool (orderOf prime x) (unaryPred p)
  have picked :
      {x : ZMod p //
        findBool predicate (nonzeroResidues prime) = some x /\
          predicate x = true} :=
    findBool_success_of_filter_pos predicate
      (nonzeroResidues prime) layerPositive
  refine
    { result := picked.val
      found := ?_ }
  unfold primitiveRootSearch
  rw [primitiveRootSearchFrom_eq_findBool prime (nonzeroResidues prime)]
  exact picked.property.left

theorem primitive_root_exists_of_topOrderLayer_pos {p : BHist}
    (prime : NatPrime p) :
    0 < (topOrderLayer prime).length ->
      exists g : ZMod p,
        zmodNonzero g /\
          IsPrimitiveRoot p prime.left (NatPrime_empty_absurd prime)
            (unaryPred p) g := by
  intro layerPositive
  exact primitive_root_exists_of_search_certificate prime
    (primitiveRootSearchCertificate_of_topOrderLayer_pos prime layerPositive)

end BEDC.Derived.PrimitiveRootFinal
