import BEDC.FKernel.Hist
import BEDC.MetaCIC.ClosedTerm

namespace BEDC.MetaCIC.BHistSubstrate

abbrev BHistIdx : Type := BEDC.FKernel.Hist.BHist

def bhistLen : BHistIdx → Nat
  | BEDC.FKernel.Hist.BHist.Empty => 0
  | BEDC.FKernel.Hist.BHist.e0 rest => bhistLen rest + 1
  | BEDC.FKernel.Hist.BHist.e1 rest => bhistLen rest + 1

def natToBHist : Nat → BHistIdx
  | 0 => BEDC.FKernel.Hist.BHist.Empty
  | n + 1 => BEDC.FKernel.Hist.BHist.e0 (natToBHist n)

theorem bhistLen_natToBHist (n : Nat) : bhistLen (natToBHist n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      unfold natToBHist bhistLen
      rw [ih]

def bhistPayloadToTerm : BHistIdx → Term
  | BEDC.FKernel.Hist.BHist.Empty =>
      Term.var 2
  | BEDC.FKernel.Hist.BHist.e0 rest =>
      Term.app (Term.var 1)
        (Term.lam Term.sort
          (Term.lam Term.sort
            (Term.lam Term.sort
              (bhistPayloadToTerm rest))))
  | BEDC.FKernel.Hist.BHist.e1 rest =>
      Term.app (Term.var 0)
        (Term.lam Term.sort
          (Term.lam Term.sort
            (Term.lam Term.sort
              (bhistPayloadToTerm rest))))

def bhistToTerm (h : BHistIdx) : Term :=
  Term.lam Term.sort
    (Term.lam Term.sort
      (Term.lam Term.sort
        (bhistPayloadToTerm h)))

def bhistFromPayloadTerm? : Term → Option BHistIdx
  | Term.var 2 => some BEDC.FKernel.Hist.BHist.Empty
  | Term.app (Term.var 1)
      (Term.lam Term.sort (Term.lam Term.sort (Term.lam Term.sort rest))) =>
      match bhistFromPayloadTerm? rest with
      | some h => some (BEDC.FKernel.Hist.BHist.e0 h)
      | none => none
  | Term.app (Term.var 0)
      (Term.lam Term.sort (Term.lam Term.sort (Term.lam Term.sort rest))) =>
      match bhistFromPayloadTerm? rest with
      | some h => some (BEDC.FKernel.Hist.BHist.e1 h)
      | none => none
  | _ => none

def bhistFromTerm? : Term → Option BHistIdx
  | Term.lam Term.sort (Term.lam Term.sort (Term.lam Term.sort body)) =>
      bhistFromPayloadTerm? body
  | _ => none

private theorem closedAt_succ_local (d : Idx) (t : Term) :
    ClosedAt d t → ClosedAt (d + 1) t := by
  intro h
  induction h with
  | varClosed hlt =>
      apply ClosedAt.varClosed
      exact Nat.lt_trans hlt (Nat.lt_succ_self _)
  | appClosed _ _ ihf iha =>
      apply ClosedAt.appClosed
      · exact ihf
      · exact iha
  | lamClosed _ _ ihdom ihbody =>
      apply ClosedAt.lamClosed
      · exact ihdom
      · exact ihbody
  | piClosed _ _ ihdom ihcod =>
      apply ClosedAt.piClosed
      · exact ihdom
      · exact ihcod
  | sortClosed =>
      exact ClosedAt.sortClosed

private theorem bhistPayloadToTerm_closed_at_three (h : BHistIdx) :
    ClosedAt 3 (bhistPayloadToTerm h) := by
  induction h with
  | Empty =>
      unfold bhistPayloadToTerm
      apply ClosedAt.varClosed
      exact Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 0))
  | e0 rest ih =>
      unfold bhistPayloadToTerm
      apply ClosedAt.appClosed
      · apply ClosedAt.varClosed
        exact Nat.succ_lt_succ (Nat.zero_lt_succ 1)
      · apply ClosedAt.lamClosed
        · exact ClosedAt.sortClosed
        · apply ClosedAt.lamClosed
          · exact ClosedAt.sortClosed
          · apply ClosedAt.lamClosed
            · exact ClosedAt.sortClosed
            · exact closedAt_succ_local (3 + 1 + 1) (bhistPayloadToTerm rest)
                (closedAt_succ_local (3 + 1) (bhistPayloadToTerm rest)
                  (closedAt_succ_local 3 (bhistPayloadToTerm rest) ih))
  | e1 rest ih =>
      unfold bhistPayloadToTerm
      apply ClosedAt.appClosed
      · apply ClosedAt.varClosed
        exact Nat.zero_lt_succ 2
      · apply ClosedAt.lamClosed
        · exact ClosedAt.sortClosed
        · apply ClosedAt.lamClosed
          · exact ClosedAt.sortClosed
          · apply ClosedAt.lamClosed
            · exact ClosedAt.sortClosed
            · exact closedAt_succ_local (3 + 1 + 1) (bhistPayloadToTerm rest)
                (closedAt_succ_local (3 + 1) (bhistPayloadToTerm rest)
                  (closedAt_succ_local 3 (bhistPayloadToTerm rest) ih))

theorem bhistToTerm_closed (h : BHistIdx) : ClosedAt 0 (bhistToTerm h) := by
  unfold bhistToTerm
  apply ClosedAt.lamClosed
  · exact ClosedAt.sortClosed
  · apply ClosedAt.lamClosed
    · exact ClosedAt.sortClosed
    · apply ClosedAt.lamClosed
      · exact ClosedAt.sortClosed
      · exact bhistPayloadToTerm_closed_at_three h

private theorem tripleLam_payload_eq {a b : Term} :
    Term.lam Term.sort (Term.lam Term.sort (Term.lam Term.sort a)) =
      Term.lam Term.sort (Term.lam Term.sort (Term.lam Term.sort b)) →
    a = b := by
  intro h
  have h1 :
      Term.lam Term.sort (Term.lam Term.sort a) =
        Term.lam Term.sort (Term.lam Term.sort b) :=
    (Term.lam.inj h).right
  have h2 : Term.lam Term.sort a = Term.lam Term.sort b :=
    (Term.lam.inj h1).right
  exact (Term.lam.inj h2).right

theorem bhistPayloadToTerm_injective {h k : BHistIdx} :
    bhistPayloadToTerm h = bhistPayloadToTerm k → h = k := by
  intro hterm
  induction h generalizing k with
  | Empty =>
      cases k with
      | Empty =>
          rfl
      | e0 rest =>
          unfold bhistPayloadToTerm at hterm
          cases hterm
      | e1 rest =>
          unfold bhistPayloadToTerm at hterm
          cases hterm
  | e0 rest ih =>
      cases k with
      | Empty =>
          unfold bhistPayloadToTerm at hterm
          cases hterm
      | e0 tail =>
          unfold bhistPayloadToTerm at hterm
          have inner :
              Term.lam Term.sort
                (Term.lam Term.sort
                  (Term.lam Term.sort (bhistPayloadToTerm rest))) =
              Term.lam Term.sort
                (Term.lam Term.sort
                  (Term.lam Term.sort (bhistPayloadToTerm tail))) :=
            Term.app.inj hterm |>.right
          exact congrArg BEDC.FKernel.Hist.BHist.e0 (ih (tripleLam_payload_eq inner))
      | e1 tail =>
          unfold bhistPayloadToTerm at hterm
          cases hterm
  | e1 rest ih =>
      cases k with
      | Empty =>
          unfold bhistPayloadToTerm at hterm
          cases hterm
      | e0 tail =>
          unfold bhistPayloadToTerm at hterm
          cases hterm
      | e1 tail =>
          unfold bhistPayloadToTerm at hterm
          have inner :
              Term.lam Term.sort
                (Term.lam Term.sort
                  (Term.lam Term.sort (bhistPayloadToTerm rest))) =
              Term.lam Term.sort
                (Term.lam Term.sort
                  (Term.lam Term.sort (bhistPayloadToTerm tail))) :=
            Term.app.inj hterm |>.right
          exact congrArg BEDC.FKernel.Hist.BHist.e1 (ih (tripleLam_payload_eq inner))

theorem bhistToTerm_injective {h k : BHistIdx} :
    bhistToTerm h = bhistToTerm k → h = k := by
  intro hterm
  unfold bhistToTerm at hterm
  exact bhistPayloadToTerm_injective (tripleLam_payload_eq hterm)

end BEDC.MetaCIC.BHistSubstrate
