import BEDC.MetaCIC.Confluence.Core
import BEDC.MetaCIC.Substitution

namespace BEDC.MetaCIC

theorem nat_blt_zero_false (d : Nat) :
    Nat.blt d 0 = false := by
  cases d
  · rfl
  · rfl

theorem shift_one_preserves_closed_succ
    {cutoff n : Idx} {t : Term}
    (hle : cutoff ≤ n)
    (hclosed : ClosedAt n t) :
    ClosedAt (n + 1) (shift cutoff 1 t) := by
  induction hclosed generalizing cutoff with
  | varClosed hlt =>
      unfold shift
      cases hble : Nat.ble cutoff _ with
      | false =>
          apply ClosedAt.varClosed
          exact Nat.lt_trans hlt (Nat.lt_succ_self _)
      | true =>
          apply ClosedAt.varClosed
          exact Nat.succ_lt_succ hlt
  | appClosed _ _ ihf iha =>
      unfold shift
      apply ClosedAt.appClosed
      · exact ihf hle
      · exact iha hle
  | lamClosed _ _ ihdom ihbody =>
      unfold shift
      apply ClosedAt.lamClosed
      · exact ihdom hle
      · exact ihbody (Nat.succ_le_succ hle)
  | piClosed _ _ ihdom ihcod =>
      unfold shift
      apply ClosedAt.piClosed
      · exact ihdom hle
      · exact ihcod (Nat.succ_le_succ hle)
  | sortClosed =>
      unfold shift
      exact ClosedAt.sortClosed

theorem substitute_var_preserves_closed_at
    (d n i : Idx) (s : Term)
    (hle : d ≤ n)
    (hs : ClosedAt n s)
    (hlt : i < n + 1) :
    ClosedAt n (substitute d s (Term.var i)) := by
  unfold substitute
  cases hbeq : Nat.beq i d
  · cases hblt : Nat.blt d i
    ·
      apply ClosedAt.varClosed
      have hble_false : Nat.ble d i = false := by
        cases hble : Nat.ble d i
        · rfl
        · have hblt_true : Nat.blt d i = true :=
            nat_blt_true_of_ble_true_beq_false d i hble hbeq
          rw [hblt] at hblt_true
          cases hblt_true
      have hlt_d_succ : i < d + 1 :=
        nat_lt_succ_of_ble_false d i hble_false
      have hsucc_lt_d_succ : i + 1 < d + 1 :=
        nat_succ_lt_of_beq_false_blt_false_succ_lt d i
          hbeq hblt hlt_d_succ
      have hlt_d : i < d :=
        Nat.lt_of_succ_lt_succ hsucc_lt_d_succ
      exact Nat.lt_of_lt_of_le hlt_d hle
    ·
      cases i with
      | zero =>
          rw [nat_blt_zero_false d] at hblt
          cases hblt
      | succ i =>
          rw [Nat.succ_sub_one]
          apply ClosedAt.varClosed
          exact Nat.lt_of_succ_lt_succ hlt
  ·
    exact hs

theorem substitute_preserves_closed_at
    {d n : Idx} {s t : Term}
    (hle : d ≤ n)
    (hs : ClosedAt n s)
    (ht : ClosedAt (n + 1) t) :
    ClosedAt n (substitute d s t) := by
  induction t generalizing d n s with
  | var i =>
      cases ht with
      | varClosed hlt =>
          exact substitute_var_preserves_closed_at d n i s hle hs hlt
  | app f a ihf iha =>
      cases ht with
      | appClosed hf ha =>
          unfold substitute
          apply ClosedAt.appClosed
          · exact ihf hle hs hf
          · exact iha hle hs ha
  | lam dom body ihdom ihbody =>
      cases ht with
      | lamClosed hdom hbody =>
          unfold substitute
          apply ClosedAt.lamClosed
          · exact ihdom hle hs hdom
          · exact ihbody
              (Nat.succ_le_succ hle)
              (shift_one_preserves_closed_succ (Nat.zero_le _) hs)
              hbody
  | pi dom cod ihdom ihcod =>
      cases ht with
      | piClosed hdom hcod =>
          unfold substitute
          apply ClosedAt.piClosed
          · exact ihdom hle hs hdom
          · exact ihcod
              (Nat.succ_le_succ hle)
              (shift_one_preserves_closed_succ (Nat.zero_le _) hs)
              hcod
  | sort =>
      exact ClosedAt.sortClosed

theorem betaStep_preserves_closed {n : Idx} {t t' : Term}
    (hclosed : ClosedAt n t) (hbeta : BetaStep t t') :
    ClosedAt n t' := by
  induction hbeta generalizing n with
  | beta dom body arg =>
      cases hclosed with
      | appClosed hlam harg =>
          cases hlam with
          | lamClosed _ hbody =>
              exact substitute_preserves_closed_at (Nat.zero_le _) harg hbody
  | congApp1 f f' a _ ih =>
      cases hclosed with
      | appClosed hf ha =>
          apply ClosedAt.appClosed
          · exact ih hf
          · exact ha
  | congApp2 f a a' _ ih =>
      cases hclosed with
      | appClosed hf ha =>
          apply ClosedAt.appClosed
          · exact hf
          · exact ih ha
  | congLam d b b' _ ih =>
      cases hclosed with
      | lamClosed hd hb =>
          apply ClosedAt.lamClosed
          · exact hd
          · exact ih hb
  | congPiCod d c c' _ ih =>
      cases hclosed with
      | piClosed hd hc =>
          apply ClosedAt.piClosed
          · exact hd
          · exact ih hc
  | congPiDom d d' c _ ih =>
      cases hclosed with
      | piClosed hd hc =>
          apply ClosedAt.piClosed
          · exact ih hd
          · exact hc
  | congLamDom d d' b _ ih =>
      cases hclosed with
      | lamClosed hd hb =>
          apply ClosedAt.lamClosed
          · exact ih hd
          · exact hb

theorem betaStarStep_preserves_closed {n : Idx} {t t' : Term}
    (hclosed : ClosedAt n t) (hbeta : BetaStarStep t t') :
    ClosedAt n t' := by
  induction hbeta generalizing n with
  | refl t =>
      exact hclosed
  | step hstep _ ih =>
      exact ih (betaStep_preserves_closed hclosed hstep)

end BEDC.MetaCIC
