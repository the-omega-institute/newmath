import BEDC.MetaCIC.Syntax

namespace BEDC.MetaCIC

def Term.size : Term → Nat
  | Term.sort => 1
  | Term.var _ => 1
  | Term.lam dom body => 1 + dom.size + body.size
  | Term.pi dom cod => 1 + dom.size + cod.size
  | Term.app f a => 1 + f.size + a.size

theorem Term.size_pos (t : Term) : 1 ≤ t.size := by
  cases t with
  | var _ =>
      unfold Term.size
      exact Nat.le_refl 1
  | app f a =>
      unfold Term.size
      have hleft : 1 ≤ 1 + f.size := Nat.le_add_right 1 f.size
      have hright : 1 + f.size ≤ 1 + f.size + a.size :=
        Nat.le_add_right (1 + f.size) a.size
      exact Nat.le_trans hleft hright
  | lam dom body =>
      unfold Term.size
      have hleft : 1 ≤ 1 + dom.size := Nat.le_add_right 1 dom.size
      have hright : 1 + dom.size ≤ 1 + dom.size + body.size :=
        Nat.le_add_right (1 + dom.size) body.size
      exact Nat.le_trans hleft hright
  | pi dom cod =>
      unfold Term.size
      have hleft : 1 ≤ 1 + dom.size := Nat.le_add_right 1 dom.size
      have hright : 1 + dom.size ≤ 1 + dom.size + cod.size :=
        Nat.le_add_right (1 + dom.size) cod.size
      exact Nat.le_trans hleft hright
  | sort =>
      unfold Term.size
      exact Nat.le_refl 1

private theorem nat_lt_one_add_left (n m : Nat) : n < 1 + n + m := by
  have hbase : n < 1 + n := by
    rw [Nat.add_comm]
    exact Nat.lt_succ_self n
  have hle : 1 + n ≤ 1 + n + m := Nat.le_add_right (1 + n) m
  exact Nat.lt_of_lt_of_le hbase hle

private theorem nat_lt_one_add_right (n m : Nat) : m < 1 + n + m := by
  rw [Nat.add_comm 1 n]
  rw [Nat.add_assoc]
  rw [Nat.add_comm n (1 + m)]
  have hbase : m < 1 + m := by
    rw [Nat.add_comm]
    exact Nat.lt_succ_self m
  have hle : 1 + m ≤ 1 + m + n := Nat.le_add_right (1 + m) n
  exact Nat.lt_of_lt_of_le hbase hle

theorem Term.size_lam_dom_lt (dom body : Term) :
    dom.size < (Term.lam dom body).size := by
  change dom.size < 1 + dom.size + body.size
  exact nat_lt_one_add_left dom.size body.size

theorem Term.size_lam_body_lt (dom body : Term) :
    body.size < (Term.lam dom body).size := by
  change body.size < 1 + dom.size + body.size
  exact nat_lt_one_add_right dom.size body.size

theorem Term.size_pi_dom_lt (dom cod : Term) :
    dom.size < (Term.pi dom cod).size := by
  change dom.size < 1 + dom.size + cod.size
  exact nat_lt_one_add_left dom.size cod.size

theorem Term.size_pi_cod_lt (dom cod : Term) :
    cod.size < (Term.pi dom cod).size := by
  change cod.size < 1 + dom.size + cod.size
  exact nat_lt_one_add_right dom.size cod.size

theorem Term.size_app_fn_lt (f a : Term) :
    f.size < (Term.app f a).size := by
  change f.size < 1 + f.size + a.size
  exact nat_lt_one_add_left f.size a.size

theorem Term.size_app_arg_lt (f a : Term) :
    a.size < (Term.app f a).size := by
  change a.size < 1 + f.size + a.size
  exact nat_lt_one_add_right f.size a.size

theorem Term.size_shift (cutoff amount : Idx) (t : Term) :
    (shift cutoff amount t).size = t.size := by
  induction t generalizing cutoff with
  | var i =>
      unfold shift
      cases Nat.ble cutoff i
      · rfl
      · rfl
  | app f a ihf iha =>
      unfold shift
      change
        1 + (shift cutoff amount f).size + (shift cutoff amount a).size =
          1 + f.size + a.size
      rw [ihf cutoff]
      rw [iha cutoff]
  | lam dom body ihdom ihbody =>
      unfold shift
      change
        1 + (shift cutoff amount dom).size + (shift (cutoff + 1) amount body).size =
          1 + dom.size + body.size
      rw [ihdom cutoff]
      rw [ihbody (cutoff + 1)]
  | pi dom cod ihdom ihcod =>
      unfold shift
      change
        1 + (shift cutoff amount dom).size + (shift (cutoff + 1) amount cod).size =
          1 + dom.size + cod.size
      rw [ihdom cutoff]
      rw [ihcod (cutoff + 1)]
  | sort => rfl

theorem Term.size_induction_bounded {P : Term → Prop}
    (step : ∀ t : Term, (∀ u : Term, u.size < t.size → P u) → P t) :
    ∀ n t, t.size < n → P t := by
  intro n
  induction n with
  | zero =>
      intro t hlt
      exact False.elim (Nat.not_lt_zero t.size hlt)
  | succ n ih =>
      intro t hlt
      exact step t (fun u hsub =>
        ih u (Nat.lt_of_lt_of_le hsub (Nat.le_of_lt_succ hlt)))

theorem Term.size_induction {P : Term → Prop}
    (step : ∀ t : Term, (∀ u : Term, u.size < t.size → P u) → P t) :
    ∀ t : Term, P t := by
  intro t
  exact Term.size_induction_bounded step (t.size + 1) t (Nat.lt_succ_self t.size)

end BEDC.MetaCIC
