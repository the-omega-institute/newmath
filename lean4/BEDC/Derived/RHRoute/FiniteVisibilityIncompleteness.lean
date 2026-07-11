import BEDC.Derived.RHRoute.IntervalMatrixPSD.FormalPoly

namespace BEDC.Derived.RHRoute.FiniteVisibility

open BEDC.Derived.RHRoute.IntervalMatrixPSD.FormalPoly

private def coeffAt (fallback : QRat) : Poly -> Nat -> QRat
  | [], _ => fallback
  | x :: _, 0 => x
  | _ :: xs, Nat.succ k => coeffAt fallback xs k

def coeff (p : Poly) (k : Nat) : QRat :=
  coeffAt qzero p k

def JetEq (N : Nat) (p q : Poly) : Prop :=
  ∀ k, k ≤ N → coeff p k = coeff q k

def extendAt (p : Poly) (idx : Nat) (c : QRat) : Poly :=
  p ++ List.replicate (idx - p.length) qzero ++ [c]

private theorem coeffAt_of_length_le (xs : Poly) (fallback : QRat)
    {k : Nat} (hk : xs.length ≤ k) :
    coeffAt fallback xs k = fallback := by
  induction xs generalizing k with
  | nil =>
      rfl
  | cons x xs ih =>
      cases k with
      | zero =>
          cases hk
      | succ k =>
          exact ih (Nat.le_of_succ_le_succ hk)

private theorem coeffAt_append_left (xs ys : Poly) (fallback : QRat)
    {k : Nat} (hk : k < xs.length) :
    coeffAt fallback (xs ++ ys) k = coeffAt fallback xs k := by
  induction xs generalizing k with
  | nil =>
      cases hk
  | cons x xs ih =>
      cases k with
      | zero =>
          rfl
      | succ k =>
          exact ih (Nat.lt_of_succ_lt_succ hk)

private theorem coeffAt_append_right (xs ys : Poly) (fallback : QRat)
    {k : Nat} (hk : xs.length ≤ k) :
    coeffAt fallback (xs ++ ys) k = coeffAt fallback ys (k - xs.length) := by
  induction xs generalizing k with
  | nil =>
      rfl
  | cons x xs ih =>
      cases k with
      | zero =>
          cases hk
      | succ k =>
          change coeffAt fallback (xs ++ ys) k =
            coeffAt fallback ys (Nat.succ k - Nat.succ xs.length)
          rw [Nat.succ_sub_succ]
          exact ih (Nat.le_of_succ_le_succ hk)

private theorem coeffAt_replicate_lt (a fallback : QRat)
    {n k : Nat} (hk : k < n) :
    coeffAt fallback (List.replicate n a) k = a := by
  induction n generalizing k with
  | zero =>
      cases hk
  | succ n ih =>
      cases k with
      | zero =>
          rfl
      | succ k =>
          exact ih (Nat.lt_of_succ_lt_succ hk)

private theorem append_assoc_pure {α : Type} :
    ∀ (xs ys zs : List α), (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
  | [], _, _ => rfl
  | x :: xs, ys, zs => congrArg (List.cons x) (append_assoc_pure xs ys zs)

private theorem replicate_length_pure (a : QRat) :
    ∀ n, (List.replicate n a).length = n
  | 0 => rfl
  | Nat.succ n => congrArg Nat.succ (replicate_length_pure a n)

private theorem sub_lt_sub_right_pure {a b c : Nat} (hca : c ≤ a) (hab : a < b) :
    a - c < b - c := by
  induction c generalizing a b with
  | zero =>
      exact hab
  | succ c ih =>
      cases a with
      | zero =>
          cases hca
      | succ a =>
          cases b with
          | zero =>
              cases hab
          | succ b =>
              rw [Nat.succ_sub_succ, Nat.succ_sub_succ]
              exact ih (Nat.le_of_succ_le_succ hca) (Nat.lt_of_succ_lt_succ hab)

private theorem le_max_left_pure (a b : Nat) : a ≤ Nat.max a b := by
  unfold Nat.max
  unfold Max.max
  unfold Nat.instMax
  unfold maxOfLe
  change a ≤ (if a ≤ b then b else a)
  cases Decidable.em (a ≤ b) with
  | inl h =>
      rw [if_pos h]
      exact h
  | inr h =>
      rw [if_neg h]
      exact Nat.le_refl a

private theorem le_max_right_pure (a b : Nat) : b ≤ Nat.max a b := by
  unfold Nat.max
  unfold Max.max
  unfold Nat.instMax
  unfold maxOfLe
  change b ≤ (if a ≤ b then b else a)
  cases Decidable.em (a ≤ b) with
  | inl h =>
      rw [if_pos h]
      exact Nat.le_refl b
  | inr h =>
      rw [if_neg h]
      exact Nat.le_of_not_ge h

private theorem coeff_extendAt_lo (p : Poly) (idx : Nat) (c : QRat)
    (k : Nat) (hk : k < idx) :
    coeff (extendAt p idx c) k = coeff p k := by
  unfold coeff extendAt
  cases Nat.lt_or_ge k p.length with
  | inl hkp =>
      calc
        coeffAt qzero (p ++ List.replicate (idx - p.length) qzero ++ [c]) k
            = coeffAt qzero (p ++ (List.replicate (idx - p.length) qzero ++ [c])) k := by
                rw [append_assoc_pure]
        _ = coeffAt qzero p k := by
                exact coeffAt_append_left p (List.replicate (idx - p.length) qzero ++ [c]) qzero hkp
  | inr hpk =>
      have hp : coeffAt qzero p k = qzero :=
        coeffAt_of_length_le p qzero hpk
      have hkrep : k - p.length < idx - p.length :=
        sub_lt_sub_right_pure hpk hk
      calc
        coeffAt qzero (p ++ List.replicate (idx - p.length) qzero ++ [c]) k
            = coeffAt qzero (p ++ (List.replicate (idx - p.length) qzero ++ [c])) k := by
                rw [append_assoc_pure]
        _ = coeffAt qzero (List.replicate (idx - p.length) qzero ++ [c]) (k - p.length) := by
                exact coeffAt_append_right p (List.replicate (idx - p.length) qzero ++ [c]) qzero hpk
        _ = coeffAt qzero (List.replicate (idx - p.length) qzero) (k - p.length) := by
                exact coeffAt_append_left (List.replicate (idx - p.length) qzero) [c] qzero
                  (by
                    rw [replicate_length_pure]
                    exact hkrep)
        _ = qzero := by
                exact coeffAt_replicate_lt qzero qzero hkrep
        _ = coeffAt qzero p k := hp.symm

private theorem coeff_extendAt_hi (p : Poly) (idx : Nat) (c : QRat)
    (hidx : p.length ≤ idx) :
    coeff (extendAt p idx c) idx = c := by
  unfold coeff extendAt
  have hrepLen : (List.replicate (idx - p.length) qzero).length = idx - p.length := by
    exact replicate_length_pure qzero (idx - p.length)
  have htail :
      (idx - p.length) -
          (List.replicate (idx - p.length) qzero).length = 0 := by
    rw [hrepLen, Nat.sub_self]
  calc
    coeffAt qzero (p ++ List.replicate (idx - p.length) qzero ++ [c]) idx
        = coeffAt qzero (p ++ (List.replicate (idx - p.length) qzero ++ [c])) idx := by
            rw [append_assoc_pure]
    _ = coeffAt qzero (List.replicate (idx - p.length) qzero ++ [c]) (idx - p.length) := by
            exact coeffAt_append_right p (List.replicate (idx - p.length) qzero ++ [c]) qzero hidx
    _ = coeffAt qzero [c] ((idx - p.length) -
          (List.replicate (idx - p.length) qzero).length) := by
            exact coeffAt_append_right (List.replicate (idx - p.length) qzero) [c] qzero
              (Nat.le_of_eq hrepLen)
    _ = coeffAt qzero [c] 0 := by
            rw [htail]
    _ = c := by
            rfl

theorem jet_extendAt_invisible (N : Nat) (p : Poly) (c : QRat) (idx : Nat)
    (hidx : N < idx) :
    JetEq N p (extendAt p idx c) := by
  intro k hk
  exact (coeff_extendAt_lo p idx c k (Nat.lt_of_le_of_lt hk hidx)).symm

theorem qOfNat_ne (a b : Nat) (h : a ≠ b) :
    qOfNat a ≠ qOfNat b := by
  intro he
  apply h
  have hnum : (qOfNat a).num = (qOfNat b).num :=
    congrArg QRat.num he
  exact Int.ofNat.inj hnum

def fvIdx (N : Nat) (p : Poly) : Nat :=
  Nat.max (N + 1) p.length

def fvFamily (N : Nat) (p : Poly) (m : Nat) : Poly :=
  extendAt p (fvIdx N p) (qOfNat (m + 1))

theorem fvFamily_shares_jet (N : Nat) (p : Poly) (m : Nat) :
    JetEq N p (fvFamily N p m) := by
  unfold fvFamily
  apply jet_extendAt_invisible
  unfold fvIdx
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self N)
    (le_max_left_pure (N + 1) p.length)

theorem fvFamily_injective (N : Nat) (p : Poly) (m n : Nat)
    (h : m ≠ n) :
    fvFamily N p m ≠ fvFamily N p n := by
  intro he
  apply h
  have hidx : p.length ≤ fvIdx N p := by
    unfold fvIdx
    exact le_max_right_pure (N + 1) p.length
  have hcoeff :
      coeff (fvFamily N p m) (fvIdx N p) =
        coeff (fvFamily N p n) (fvIdx N p) :=
    congrArg (fun r : Poly => coeff r (fvIdx N p)) he
  have hm :
      coeff (fvFamily N p m) (fvIdx N p) = qOfNat (m + 1) := by
    unfold fvFamily
    exact coeff_extendAt_hi p (fvIdx N p) (qOfNat (m + 1)) hidx
  have hn :
      coeff (fvFamily N p n) (fvIdx N p) = qOfNat (n + 1) := by
    unfold fvFamily
    exact coeff_extendAt_hi p (fvIdx N p) (qOfNat (n + 1)) hidx
  have hq : qOfNat (m + 1) = qOfNat (n + 1) :=
    hm.symm.trans (hcoeff.trans hn)
  have hsucc : m + 1 ≠ n + 1 := by
    intro hs
    apply h
    exact Nat.succ.inj hs
  exact (False.elim (qOfNat_ne (m + 1) (n + 1) hsucc hq))

example : JetEq 1 [qOfNat 3, qOfNat 5]
    (fvFamily 1 [qOfNat 3, qOfNat 5] 7) :=
  fvFamily_shares_jet 1 _ 7

example :
    fvFamily 1 [qOfNat 3, qOfNat 5] 0 ≠
      fvFamily 1 [qOfNat 3, qOfNat 5] 4 :=
  fvFamily_injective 1 _ 0 4 (by
    intro h
    cases h)

end BEDC.Derived.RHRoute.FiniteVisibility
