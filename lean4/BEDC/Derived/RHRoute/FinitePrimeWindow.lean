import BEDC.Derived.IntUp.Arithmetic
import BEDC.Derived.PrimeUp

namespace BEDC.Derived.RHRoute.FinitePrimeWindow

open BEDC.Derived.IntUp
open BEDC.Derived.PrimeUp

inductive NoDup {α : Type u} : List α -> Prop where
  | nil : NoDup []
  | cons {x : α} {xs : List α} : x ∉ xs -> NoDup xs -> NoDup (x :: xs)

inductive All {α : Type u} (P : α -> Prop) : List α -> Prop where
  | nil : All P []
  | cons {x : α} {xs : List α} : P x -> All P xs -> All P (x :: xs)

def IsPrime (p : Nat) : Prop :=
  NatPrime (natToUnary p)

namespace All

theorem mem {α : Type u} {P : α -> Prop} {x : α} :
    ∀ {xs : List α}, All P xs -> x ∈ xs -> P x
  | [], all, member => by
      cases member
  | y :: ys, all, member => by
      cases all with
      | cons hy hys =>
          cases member with
          | head =>
              exact hy
          | tail _ tailMember =>
              exact mem hys tailMember

theorem append {α : Type u} {P : α -> Prop} :
    ∀ {xs ys : List α}, All P xs -> All P ys -> All P (xs ++ ys)
  | [], ys, _, hys => hys
  | x :: xs, ys, hxs, hys => by
      cases hxs with
      | cons hx hxsTail =>
          exact All.cons hx (append hxsTail hys)

theorem filter {α : Type u} {P : α -> Prop} {keep : α -> Bool} :
    ∀ {xs : List α}, All P xs -> All P (xs.filter keep)
  | [], _ => All.nil
  | x :: xs, hxs => by
      cases hxs with
      | cons hx hxsTail =>
          unfold List.filter
          cases keep x with
          | false =>
              exact filter hxsTail
          | true =>
              exact All.cons hx (filter hxsTail)

end All

namespace NoDup

theorem tail {α : Type u} {x : α} {xs : List α} :
    NoDup (x :: xs) -> NoDup xs := by
  intro nodup
  cases nodup with
  | cons _ tailNodup =>
      exact tailNodup

theorem head_not_mem {α : Type u} {x : α} {xs : List α} :
    NoDup (x :: xs) -> x ∉ xs := by
  intro nodup
  cases nodup with
  | cons absent _ =>
      exact absent

end NoDup

def listMemNat (p : Nat) : List Nat -> Bool
  | [] => false
  | q :: qs => if p = q then true else listMemNat p qs

theorem listMemNat_true {p : Nat} :
    ∀ {xs : List Nat}, listMemNat p xs = true -> p ∈ xs
  | [], h => by
      cases h
  | q :: qs, h => by
      unfold listMemNat at h
      by_cases hpq : p = q
      · rw [if_pos hpq] at h
        exact hpq.symm ▸ List.Mem.head qs
      · rw [if_neg hpq] at h
        exact List.Mem.tail q (listMemNat_true h)

theorem listMemNat_of_mem {p : Nat} :
    ∀ {xs : List Nat}, p ∈ xs -> listMemNat p xs = true
  | [], h => by
      cases h
  | q :: qs, h => by
      unfold listMemNat
      cases h with
      | head =>
          rw [if_pos rfl]
      | tail _ tailMember =>
          by_cases hpq : p = q
          · rw [if_pos hpq]
          · rw [if_neg hpq]
            exact listMemNat_of_mem tailMember

theorem listMemNat_false_not_mem {p : Nat} {xs : List Nat} :
    listMemNat p xs = false -> Not (p ∈ xs) := by
  intro h member
  have present : listMemNat p xs = true := listMemNat_of_mem member
  rw [present] at h
  cases h

theorem not_mem_of_listMemNat_false {p : Nat} {xs : List Nat} :
    listMemNat p xs = false -> p ∉ xs :=
  listMemNat_false_not_mem

theorem listMemNat_false_of_not_mem {p : Nat} :
    ∀ {xs : List Nat}, p ∉ xs -> listMemNat p xs = false
  | [], _ => rfl
  | q :: qs, absent => by
      unfold listMemNat
      by_cases hpq : p = q
      · have headMember : p ∈ q :: qs := hpq.symm ▸ List.Mem.head qs
        exact False.elim (absent headMember)
      · rw [if_neg hpq]
        exact listMemNat_false_of_not_mem (fun tailMember =>
          absent (List.Mem.tail q tailMember))

theorem mem_cons_of_ne {p q : Nat} {qs : List Nat} :
    p ∈ q :: qs -> p ≠ q -> p ∈ qs := by
  intro member neq
  cases member with
  | head =>
      exact False.elim (neq rfl)
  | tail _ tailMember =>
      exact tailMember

def insertFreshNat (p : Nat) (xs : List Nat) : List Nat :=
  match listMemNat p xs with
  | true => xs
  | false => p :: xs

theorem mem_insertFreshNat_self (p : Nat) (xs : List Nat) :
    p ∈ insertFreshNat p xs := by
  unfold insertFreshNat
  cases h : listMemNat p xs with
  | false =>
      exact List.Mem.head xs
  | true =>
      exact listMemNat_true h

theorem mem_insertFreshNat_of_mem {p q : Nat} {xs : List Nat} :
    q ∈ xs -> q ∈ insertFreshNat p xs := by
  intro member
  unfold insertFreshNat
  cases listMemNat p xs with
  | false =>
      exact List.Mem.tail p member
  | true =>
      exact member

theorem mem_insertFreshNat_cases {p q : Nat} {xs : List Nat} :
    q ∈ insertFreshNat p xs -> q = p ∨ q ∈ xs := by
  intro member
  unfold insertFreshNat at member
  cases h : listMemNat p xs with
  | true =>
      rw [h] at member
      exact Or.inr member
  | false =>
      rw [h] at member
      cases member with
      | head =>
          exact Or.inl rfl
      | tail _ tailMember =>
          exact Or.inr tailMember

theorem nodup_insertFreshNat {p : Nat} {xs : List Nat} :
    NoDup xs -> NoDup (insertFreshNat p xs) := by
  intro nodup
  unfold insertFreshNat
  cases h : listMemNat p xs with
  | true =>
      exact nodup
  | false =>
      exact NoDup.cons (not_mem_of_listMemNat_false h) nodup

theorem all_prime_insertFreshNat {p : Nat} {xs : List Nat} :
    IsPrime p -> All IsPrime xs -> All IsPrime (insertFreshNat p xs) := by
  intro pPrime allXs
  unfold insertFreshNat
  cases h : listMemNat p xs with
  | true =>
      exact allXs
  | false =>
      exact All.cons pPrime allXs

def unionList : List Nat -> List Nat -> List Nat
  | [], ys => ys
  | x :: xs, ys => unionList xs (insertFreshNat x ys)

def interList : List Nat -> List Nat -> List Nat
  | [], _ => []
  | x :: xs, ys =>
      match listMemNat x ys with
      | true => x :: interList xs ys
      | false => interList xs ys

theorem mem_unionList_right :
    ∀ {xs ys : List Nat} {p : Nat}, p ∈ ys -> p ∈ unionList xs ys
  | [], ys, p, member => member
  | x :: xs, ys, p, member => by
      exact mem_unionList_right
        (xs := xs) (ys := insertFreshNat x ys) (p := p)
        (mem_insertFreshNat_of_mem member)

theorem mem_unionList_left :
    ∀ {xs ys : List Nat} {p : Nat}, p ∈ xs -> p ∈ unionList xs ys
  | [], _ys, _p, member => by
      cases member
  | x :: xs, ys, p, member => by
      cases member with
      | head =>
          exact mem_unionList_right
            (xs := xs) (ys := insertFreshNat x ys) (p := x)
            (mem_insertFreshNat_self x ys)
      | tail _ tailMember =>
          exact mem_unionList_left
            (xs := xs) (ys := insertFreshNat x ys) (p := p) tailMember

theorem nodup_unionList :
    ∀ {xs ys : List Nat}, NoDup xs -> NoDup ys -> NoDup (unionList xs ys)
  | [], ys, _xsNodup, ysNodup => ysNodup
  | x :: xs, ys, xsNodup, ysNodup => by
      exact nodup_unionList
        (xs := xs) (ys := insertFreshNat x ys)
        (NoDup.tail xsNodup) (nodup_insertFreshNat ysNodup)

theorem all_prime_unionList :
    ∀ {xs ys : List Nat}, All IsPrime xs -> All IsPrime ys -> All IsPrime (unionList xs ys)
  | [], ys, _allXs, allYs => allYs
  | x :: xs, ys, allXs, allYs => by
      cases allXs with
      | cons xPrime xsPrime =>
          exact all_prime_unionList
            (xs := xs) (ys := insertFreshNat x ys)
            xsPrime (all_prime_insertFreshNat xPrime allYs)

theorem mem_interList_left :
    ∀ {xs ys : List Nat} {p : Nat}, p ∈ interList xs ys -> p ∈ xs
  | [], _ys, _p, member => by
      cases member
  | x :: xs, ys, p, member => by
      unfold interList at member
      cases h : listMemNat x ys with
      | true =>
          rw [h] at member
          cases member with
          | head =>
              exact List.Mem.head xs
          | tail _ tailMember =>
              exact List.Mem.tail x (mem_interList_left tailMember)
      | false =>
          rw [h] at member
          exact List.Mem.tail x (mem_interList_left member)

theorem mem_interList_right :
    ∀ {xs ys : List Nat} {p : Nat}, p ∈ interList xs ys -> p ∈ ys
  | [], _ys, _p, member => by
      cases member
  | x :: xs, ys, p, member => by
      unfold interList at member
      cases h : listMemNat x ys with
      | true =>
          rw [h] at member
          cases member with
          | head =>
              exact listMemNat_true h
          | tail _ tailMember =>
              exact mem_interList_right tailMember
      | false =>
          rw [h] at member
          exact mem_interList_right member

theorem mem_interList_of_mem_left_right :
    ∀ {xs ys : List Nat} {p : Nat}, p ∈ xs -> p ∈ ys -> p ∈ interList xs ys
  | [], _ys, _p, leftMember, _rightMember => by
      cases leftMember
  | x :: xs, ys, p, leftMember, rightMember => by
      unfold interList
      cases leftMember with
      | head =>
          have present : listMemNat x ys = true := listMemNat_of_mem rightMember
          rw [present]
          exact List.Mem.head (interList xs ys)
      | tail _ tailMember =>
          cases h : listMemNat x ys with
          | true =>
              exact List.Mem.tail x
                (mem_interList_of_mem_left_right tailMember rightMember)
          | false =>
              exact mem_interList_of_mem_left_right tailMember rightMember

theorem nodup_interList :
    ∀ {xs ys : List Nat}, NoDup xs -> NoDup (interList xs ys)
  | [], _ys, _xsNodup => by
      exact NoDup.nil
  | x :: xs, ys, xsNodup => by
      have xAbsent : x ∉ xs := NoDup.head_not_mem xsNodup
      have xsTailNodup : NoDup xs := NoDup.tail xsNodup
      unfold interList
      cases h : listMemNat x ys with
      | true =>
          exact NoDup.cons
            (fun xInInter => xAbsent (mem_interList_left xInInter))
            (nodup_interList xsTailNodup)
      | false =>
          exact nodup_interList xsTailNodup

theorem all_prime_interList :
    ∀ {xs ys : List Nat}, All IsPrime xs -> All IsPrime (interList xs ys)
  | [], _ys, _allXs => All.nil
  | x :: xs, ys, allXs => by
      cases allXs with
      | cons xPrime xsPrime =>
          unfold interList
          cases h : listMemNat x ys with
          | true =>
              exact All.cons xPrime (all_prime_interList xsPrime)
          | false =>
              exact all_prime_interList xsPrime

structure PrimeWindow where
  elems : List Nat
  nodup : NoDup elems
  all_prime : All IsPrime elems

namespace PrimeWindow

def mem (p : Nat) (W : PrimeWindow) : Prop :=
  p ∈ W.elems

def union (W₁ W₂ : PrimeWindow) : PrimeWindow where
  elems := unionList W₁.elems W₂.elems
  nodup := nodup_unionList W₁.nodup W₂.nodup
  all_prime := all_prime_unionList W₁.all_prime W₂.all_prime

def inter (W₁ W₂ : PrimeWindow) : PrimeWindow where
  elems := interList W₁.elems W₂.elems
  nodup := nodup_interList W₁.nodup
  all_prime := all_prime_interList W₁.all_prime

theorem mem_union_left {p : Nat} {W₁ W₂ : PrimeWindow} :
    W₁.mem p -> (union W₁ W₂).mem p := by
  intro member
  exact mem_unionList_left member

theorem mem_union_right {p : Nat} {W₁ W₂ : PrimeWindow} :
    W₂.mem p -> (union W₁ W₂).mem p := by
  intro member
  exact mem_unionList_right member

theorem mem_inter_left {p : Nat} {W₁ W₂ : PrimeWindow} :
    (inter W₁ W₂).mem p -> W₁.mem p := by
  intro member
  exact mem_interList_left member

theorem mem_inter_right {p : Nat} {W₁ W₂ : PrimeWindow} :
    (inter W₁ W₂).mem p -> W₂.mem p := by
  intro member
  exact mem_interList_right member

theorem mem_inter_of_mem {p : Nat} {W₁ W₂ : PrimeWindow} :
    W₁.mem p -> W₂.mem p -> (inter W₁ W₂).mem p := by
  intro left right
  exact mem_interList_of_mem_left_right left right

theorem all_prime_union (W₁ W₂ : PrimeWindow) :
    All IsPrime (union W₁ W₂).elems := by
  exact (union W₁ W₂).all_prime

theorem nodup_union (W₁ W₂ : PrimeWindow) :
    NoDup (union W₁ W₂).elems := by
  exact (union W₁ W₂).nodup

end PrimeWindow

structure LocalTest (α : Type u) where
  run : PrimeWindow -> α -> Bool
  predicate : PrimeWindow -> α -> Prop
  sound : (W : PrimeWindow) -> (x : α) -> run W x = true -> predicate W x

def LocalPredicate (T : LocalTest α) (W : PrimeWindow) (x : α) : Prop :=
  T.predicate W x

def OverlapAgree (T : LocalTest α) (W₁ W₂ : PrimeWindow) (p : Nat) (x : α) : Prop :=
  W₁.mem p -> W₂.mem p -> T.run W₁ x = T.run W₂ x

structure WindowCompatible (T : LocalTest α) (W₁ W₂ : PrimeWindow) (x : α) where
  left_pass : T.run W₁ x = true
  right_pass : T.run W₂ x = true
  agree_on_overlap :
    (p : Nat) -> OverlapAgree T W₁ W₂ p x

structure GluedWindowCertificate (T : LocalTest α) (W₁ W₂ : PrimeWindow) (x : α) where
  union_window : PrimeWindow
  union_is_union : union_window.elems = (PrimeWindow.union W₁ W₂).elems
  left_sound : LocalPredicate T W₁ x
  right_sound : LocalPredicate T W₂ x
  overlap_consistent :
    (p : Nat) -> OverlapAgree T W₁ W₂ p x
  left_embeds :
    (p : Nat) -> W₁.mem p -> union_window.mem p
  right_embeds :
    (p : Nat) -> W₂.mem p -> union_window.mem p

def finite_prime_window_gluing_certificate
    {α : Type u} (T : LocalTest α) (W₁ W₂ : PrimeWindow) (x : α)
    (h : WindowCompatible T W₁ W₂ x) :
    GluedWindowCertificate T W₁ W₂ x where
  union_window := PrimeWindow.union W₁ W₂
  union_is_union := rfl
  left_sound := T.sound W₁ x h.left_pass
  right_sound := T.sound W₂ x h.right_pass
  overlap_consistent := h.agree_on_overlap
  left_embeds := by
    intro p member
    exact PrimeWindow.mem_union_left member
  right_embeds := by
    intro p member
    exact PrimeWindow.mem_union_right member

theorem finite_prime_window_gluing
    {α : Type u} (T : LocalTest α) (W₁ W₂ : PrimeWindow) (x : α)
    (h : WindowCompatible T W₁ W₂ x) :
    ∃ cert : GluedWindowCertificate T W₁ W₂ x,
      cert.union_window.elems = (PrimeWindow.union W₁ W₂).elems ∧
        ((p : Nat) -> W₁.mem p -> cert.union_window.mem p) ∧
          ((p : Nat) -> W₂.mem p -> cert.union_window.mem p) := by
  exact ⟨finite_prime_window_gluing_certificate T W₁ W₂ x h,
    And.intro rfl
      (And.intro
        (fun p member => PrimeWindow.mem_union_left member)
        (fun p member => PrimeWindow.mem_union_right member))⟩

end BEDC.Derived.RHRoute.FinitePrimeWindow
