import BEDC.Derived.Window6FibonacciCount

namespace BEDC.Derived.Window6FactorImageCount

abbrev fib : Nat -> Nat :=
  BEDC.Derived.Window6Fibonacci.fib

abbrev stableCount : Nat -> Nat :=
  BEDC.Derived.Window6Fibonacci.stableCount

def contains {α : Type} [DecidableEq α] (a : α) : List α -> Bool
  | [] => false
  | b :: bs =>
      match decEq a b with
      | isTrue _ => true
      | isFalse _ => contains a bs

def dedup {α : Type} [DecidableEq α] : List α -> List α
  | [] => []
  | a :: as =>
      match contains a as with
      | true => dedup as
      | false => a :: dedup as

def imageCount {α β : Type} [DecidableEq β] (f : α -> β) (xs : List α) : Nat :=
  (dedup (xs.map f)).length

def InjectiveOnList {α β : Type} (f : α -> β) (xs : List α) : Prop :=
  (xs.map f).Nodup

def extendZero (xs : List Bool) : List Bool :=
  false :: xs

def extendOne (xs : List Bool) : List Bool :=
  true :: xs

def stableStateWords : Nat -> List (List Bool) × List (List Bool)
  | 0 => ([[]], [[]])
  | n + 1 =>
      let prev := stableStateWords n
      (prev.1.map extendZero ++ prev.2.map extendOne, prev.1.map extendZero)

def stableWords (m : Nat) : List (List Bool) :=
  (stableStateWords m).1

theorem contains_true_mem {α : Type} [DecidableEq α] {a : α} :
    forall {xs : List α}, contains a xs = true -> a ∈ xs
  | [], h => by
      cases h
  | b :: bs, h => by
      unfold contains at h
      cases hd : decEq a b with
      | isTrue heq =>
          cases heq
          exact List.Mem.head bs
      | isFalse _ =>
          rw [hd] at h
          exact List.Mem.tail b (contains_true_mem h)

theorem contains_false_not_mem {α : Type} [DecidableEq α] {a : α} :
    forall {xs : List α}, contains a xs = false -> ¬a ∈ xs
  | [], _ => by
      intro hm
      cases hm
  | b :: bs, h => by
      unfold contains at h
      cases hd : decEq a b with
      | isTrue _ =>
          rw [hd] at h
          cases h
      | isFalse hne =>
          rw [hd] at h
          intro hm
          cases hm with
          | head => exact hne rfl
          | tail _ ht => exact contains_false_not_mem h ht

theorem contains_false_of_not_mem {α : Type} [DecidableEq α] {a : α} :
    forall {xs : List α}, (¬a ∈ xs) -> contains a xs = false
  | [], _ => by
      rfl
  | b :: bs, h => by
      unfold contains
      cases decEq a b with
      | isTrue heq =>
          cases heq
          exact False.elim (h (List.Mem.head bs))
      | isFalse _ =>
          exact contains_false_of_not_mem
            (fun ht => h (List.Mem.tail b ht))

theorem dedup_mem_forward {α : Type} [DecidableEq α] {a : α} :
    forall {xs : List α}, a ∈ dedup xs -> a ∈ xs
  | [], h => by
      cases h
  | b :: bs, h => by
      unfold dedup at h
      cases hc : contains b bs
      · rw [hc] at h
        cases h with
        | head =>
            exact List.Mem.head bs
        | tail _ htail =>
            exact List.Mem.tail b (dedup_mem_forward htail)
      · rw [hc] at h
        exact List.Mem.tail b (dedup_mem_forward h)

theorem dedup_length_le {α : Type} [DecidableEq α] :
    forall xs : List α, (dedup xs).length <= xs.length
  | [] => by
      exact Nat.le_refl 0
  | a :: as => by
      unfold dedup
      cases contains a as
      ·
        exact Nat.succ_le_succ (dedup_length_le as)
      ·
        exact Nat.le_trans (dedup_length_le as) (Nat.le_succ as.length)

theorem dedup_nodup {α : Type} [DecidableEq α] :
    forall xs : List α, (dedup xs).Nodup
  | [] => by
      exact List.Pairwise.nil
  | a :: as => by
      unfold dedup
      cases hc : contains a as
      ·
        constructor
        · intro x hx heq
          cases heq
          exact contains_false_not_mem hc (dedup_mem_forward hx)
        · exact dedup_nodup as
      ·
        exact dedup_nodup as

theorem nodup_tail_of_cons {α : Type} {a : α} {as : List α} :
    (a :: as).Nodup -> as.Nodup := by
  intro h
  cases h with
  | cons _ htail => exact htail

theorem not_mem_tail_of_nodup_cons {α : Type} {a : α} {as : List α} :
    (a :: as).Nodup -> ¬a ∈ as := by
  intro h
  cases h with
  | cons hrel _ =>
      intro ha
      exact hrel a ha rfl

theorem dedup_eq_self_of_nodup {α : Type} [DecidableEq α] :
    forall {xs : List α}, xs.Nodup -> dedup xs = xs
  | [], _ => by
      rfl
  | a :: as, hnodup => by
      have hnot : ¬a ∈ as := not_mem_tail_of_nodup_cons hnodup
      have htail : as.Nodup := nodup_tail_of_cons hnodup
      unfold dedup
      rw [contains_false_of_not_mem hnot, dedup_eq_self_of_nodup htail]

theorem nodup_of_length_eq_dedup_length {α : Type} [DecidableEq α] :
    forall {xs : List α}, (dedup xs).length = xs.length -> xs.Nodup
  | [], _ => by
      exact List.Pairwise.nil
  | a :: as, hlen => by
      unfold dedup at hlen
      cases hc : contains a as
      · rw [hc] at hlen
        change (dedup as).length + 1 = as.length + 1 at hlen
        have htail_len : (dedup as).length = as.length := Nat.succ.inj hlen
        constructor
        · intro x hx heq
          cases heq
          exact contains_false_not_mem hc hx
        · exact nodup_of_length_eq_dedup_length htail_len
      · rw [hc] at hlen
        change (dedup as).length = as.length + 1 at hlen
        have hle : (dedup as).length <= as.length := dedup_length_le as
        have hbad : as.length + 1 <= as.length := by
          rw [← hlen]
          exact hle
        exact False.elim (Nat.not_succ_le_self as.length hbad)

theorem dedup_length_eq_length_iff_nodup {α : Type} [DecidableEq α] (xs : List α) :
    (dedup xs).length = xs.length <-> xs.Nodup := by
  constructor
  · intro h
    exact nodup_of_length_eq_dedup_length h
  · intro h
    exact congrArg List.length (dedup_eq_self_of_nodup h)

private theorem zero_add_pure (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ ih

private theorem succ_add_pure (a b : Nat) :
    Nat.succ a + b = Nat.succ (a + b) := by
  induction b with
  | zero => rfl
  | succ b ih => exact congrArg Nat.succ ih

private theorem length_append_pure {α : Type} :
    forall xs ys : List α, (xs ++ ys).length = xs.length + ys.length
  | [], ys => by
      change ys.length = 0 + ys.length
      exact (zero_add_pure ys.length).symm
  | _ :: xs, ys => by
      change ((xs ++ ys).length).succ = Nat.succ xs.length + ys.length
      rw [succ_add_pure]
      exact congrArg Nat.succ (length_append_pure xs ys)

private theorem length_map_pure {α β : Type} (f : α -> β) :
    forall xs : List α, (xs.map f).length = xs.length
  | [] => rfl
  | _ :: xs => by
      exact congrArg Nat.succ (length_map_pure f xs)

theorem imageCount_le_domain {α β : Type} [DecidableEq β] (f : α -> β) (xs : List α) :
    imageCount f xs <= xs.length := by
  unfold imageCount
  have h := dedup_length_le (xs.map f)
  exact (length_map_pure f xs) ▸ h

theorem imageCount_eq_domain_iff_injectiveOnList
    {α β : Type} [DecidableEq β] (f : α -> β) (xs : List α) :
    imageCount f xs = xs.length <-> InjectiveOnList f xs := by
  constructor
  · intro h
    unfold InjectiveOnList
    apply nodup_of_length_eq_dedup_length
    unfold imageCount at h
    exact h.trans (length_map_pure f xs).symm
  · intro h
    unfold imageCount
    unfold InjectiveOnList at h
    exact (congrArg List.length (dedup_eq_self_of_nodup h)).trans
      (length_map_pure f xs)

theorem imageCount_eq_domain_of_injectiveOnList
    {α β : Type} [DecidableEq β] (f : α -> β) (xs : List α)
    (h : InjectiveOnList f xs) :
    imageCount f xs = xs.length := by
  exact (imageCount_eq_domain_iff_injectiveOnList f xs).mpr h

theorem injectiveOnList_of_imageCount_eq_domain
    {α β : Type} [DecidableEq β] (f : α -> β) (xs : List α)
    (h : imageCount f xs = xs.length) :
    InjectiveOnList f xs := by
  exact (imageCount_eq_domain_iff_injectiveOnList f xs).mp h

theorem imageCount_strict_of_not_injectiveOnList
    {α β : Type} [DecidableEq β] (f : α -> β) (xs : List α)
    (h : ¬InjectiveOnList f xs) :
    imageCount f xs < xs.length := by
  have hle : imageCount f xs <= xs.length := imageCount_le_domain f xs
  exact Nat.lt_of_le_of_ne hle (fun heq => h ((imageCount_eq_domain_iff_injectiveOnList f xs).mp heq))

theorem stableStateWords_length_pair (m : Nat) :
    (stableStateWords m).1.length = (BEDC.Derived.Window6Fibonacci.stateCount m).total ∧
      (stableStateWords m).2.length =
        (BEDC.Derived.Window6Fibonacci.stateCount m).zeroLast := by
  induction m with
  | zero =>
      constructor
      · rfl
      · rfl
  | succ m ih =>
      unfold stableStateWords
      unfold BEDC.Derived.Window6Fibonacci.stateCount
      unfold BEDC.Derived.Window6Fibonacci.step
      constructor
      · rw [length_append_pure]
        rw [length_map_pure, length_map_pure]
        rw [ih.left, ih.right]
      · rw [length_map_pure]
        rw [ih.left]

theorem stableWords_length (m : Nat) :
    (stableWords m).length = stableCount m := by
  unfold stableWords
  unfold stableCount
  unfold BEDC.Derived.Window6Fibonacci.stableCount
  rw [(stableStateWords_length_pair m).left]

theorem stableWords_length_eq_fib (m : Nat) :
    (stableWords m).length = fib (m + 2) := by
  rw [stableWords_length]
  exact BEDC.Derived.Window6Fibonacci.stableWordCount_eq_fib m

theorem stableImageCount_le_stableCount
    {β : Type} [DecidableEq β] (m : Nat) (f : List Bool -> β) :
    imageCount f (stableWords m) <= stableCount m := by
  exact (stableWords_length m) ▸ imageCount_le_domain f (stableWords m)

theorem stableImageCount_le_fib
    {β : Type} [DecidableEq β] (m : Nat) (f : List Bool -> β) :
    imageCount f (stableWords m) <= fib (m + 2) := by
  exact (stableWords_length_eq_fib m) ▸ imageCount_le_domain f (stableWords m)

theorem stableImageCount_eq_fib_iff_decipherable
    {β : Type} [DecidableEq β] (m : Nat) (f : List Bool -> β) :
    imageCount f (stableWords m) = fib (m + 2) <->
      InjectiveOnList f (stableWords m) := by
  constructor
  · intro h
    exact injectiveOnList_of_imageCount_eq_domain f (stableWords m)
      (h.trans (stableWords_length_eq_fib m).symm)
  · intro h
    exact (imageCount_eq_domain_of_injectiveOnList f (stableWords m) h).trans
      (stableWords_length_eq_fib m)

def collisionLabel (xs : List Bool) : List Bool :=
  if xs = [false, false, false, true] then
    [false, false, false, false]
  else
    xs

def identityLabel (xs : List Bool) : List Bool :=
  xs

theorem stableWords_four_value :
    stableWords 4 =
      [[false, false, false, false],
       [false, false, false, true],
       [false, false, true, false],
       [false, true, false, false],
       [false, true, false, true],
       [true, false, false, false],
       [true, false, false, true],
       [true, false, true, false]] := by
  rfl

theorem stableWords_four_count :
    (stableWords 4).length = 8 := by
  rfl

theorem stableImageCount_four_collision :
    imageCount collisionLabel (stableWords 4) = 7 := by
  rfl

theorem stableImageCount_four_collision_lt :
    imageCount collisionLabel (stableWords 4) < (stableWords 4).length := by
  rw [stableImageCount_four_collision]
  rw [stableWords_four_count]
  decide

theorem stableImageCount_four_collision_lt_fib :
    imageCount collisionLabel (stableWords 4) < fib 6 := by
  rw [stableImageCount_four_collision]
  decide

theorem stableImageCount_four_collision_deficit :
    (stableWords 4).length - imageCount collisionLabel (stableWords 4) = 1 := by
  rfl

theorem stableImageCount_four_identity :
    imageCount identityLabel (stableWords 4) = 8 := by
  rfl

theorem stableImageCount_four_identity_eq_fib :
    imageCount identityLabel (stableWords 4) = fib 6 := by
  rfl

end BEDC.Derived.Window6FactorImageCount
