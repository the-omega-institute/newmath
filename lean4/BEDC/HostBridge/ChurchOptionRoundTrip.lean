import BEDC.MetaCIC.TypedExamples.ChurchGallery
import BEDC.MetaCIC.TypedExamples.ChurchAlgebra
import BEDC.HostBridge.MetaCICTransport
import BEDC.HostBridge.ChurchNatRoundTrip
import BEDC.HostBridge.ChurchBoolPairRoundTrip

namespace BEDC.HostBridge

open BEDC.MetaCIC

abbrev church_none : Term :=
  churchNoneTm

abbrev church_some : Term :=
  churchSomeTm

abbrev church_case_option : Term :=
  churchCaseOptionTm

abbrev church_option_ty : Term :=
  churchOptionTy

abbrev churchOptionOf (A : Term) : Term :=
  substitute 0 A churchOptionATy

abbrev churchSomeAfterType (A : Term) : Term :=
  substitute 0 A
    (Term.pi (Term.var 0)
      (Term.pi Term.sort
        (Term.pi (Term.var 0)
          (Term.pi
            (Term.pi (Term.var 3) (Term.var 2))
            (Term.var 2)))))

abbrev churchSomeAfterValue (A a : Term) : Term :=
  substitute 0 a
    (substitute 1 (shift 0 1 A)
      (Term.pi Term.sort
        (Term.pi (Term.var 0)
          (Term.pi
            (Term.pi (Term.var 3) (Term.var 2))
            (Term.var 2)))))

def hostOptionToChurch (A : Term) (encodeα : α → Term) : Option α → Term
  | none => Term.app church_none A
  | some a => Term.app (Term.app church_some A) (encodeα a)

abbrev churchOptionCaseHost (A R opt onNone onSome : Term) : Term :=
  Term.app
    (Term.app
      (Term.app
        (Term.app
          (Term.app church_case_option A)
          R)
        opt)
      onNone)
    onSome

def churchNormalToHostOption
    (decodeα : Term → Option α) : Term → Option α
  | Term.lam XDom outer =>
      match XDom with
      | Term.sort =>
          match outer with
          | Term.lam nDom inner =>
              match nDom with
              | Term.var 0 =>
                  match inner with
                  | Term.lam sDom body =>
                      match sDom with
                      | Term.pi Term.sort (Term.var 2) =>
                          match body with
                          | Term.var 1 => none
                          | Term.app (Term.var 0) payload => decodeα payload
                          | Term.var 0 => none
                          | Term.var (_ + 2) => none
                          | Term.app _ _ => none
                          | Term.lam _ _ => none
                          | Term.pi _ _ => none
                          | Term.sort => none
                      | Term.var _ => none
                      | Term.app _ _ => none
                      | Term.lam _ _ => none
                      | Term.pi _ _ => none
                      | Term.sort => none
                  | Term.var _ => none
                  | Term.app _ _ => none
                  | Term.pi _ _ => none
                  | Term.sort => none
              | Term.var (_ + 1) => none
              | Term.app _ _ => none
              | Term.lam _ _ => none
              | Term.pi _ _ => none
              | Term.sort => none
          | Term.var _ => none
          | Term.app _ _ => none
          | Term.pi _ _ => none
          | Term.sort => none
      | Term.var _ => none
      | Term.app _ _ => none
      | Term.lam _ _ => none
      | Term.pi _ _ => none
  | Term.var _ => none
  | Term.app _ _ => none
  | Term.pi _ _ => none
  | Term.sort => none

def churchToHostOption
    (decodeα : Term → Option α) (t : Term) (fuel : Nat) : Option α :=
  churchNormalToHostOption decodeα (normalizeBounded fuel t)

theorem hostOptionToChurch_typed_none
    (A : Term) (hA : HasType [] A Term.sort) :
    HasType [] (hostOptionToChurch A (fun _ : α => Term.sort) none)
      (churchOptionOf A) := by
  unfold hostOptionToChurch churchOptionOf church_none
  exact HasType.appRule []
    churchNoneTm
    A
    Term.sort
    churchOptionATy
    BEDC.MetaCIC.church_none
    hA

theorem hostOptionToChurch_typed_some
    (A : Term) (encodeα : α → Term)
    (hA : HasType [] A Term.sort)
    (typed_α : ∀ a, HasType [] (encodeα a) A)
    (a : α) :
    HasType [] (hostOptionToChurch A encodeα (some a))
      (churchSomeAfterValue A (encodeα a)) := by
  unfold hostOptionToChurch churchSomeAfterValue church_some
  exact HasType.appRule []
    (Term.app churchSomeTm A)
    (encodeα a)
    A
    (substitute 1 (shift 0 1 A)
      (Term.pi Term.sort
        (Term.pi (Term.var 0)
          (Term.pi
            (Term.pi (Term.var 3) (Term.var 2))
            (Term.var 2)))))
    (HasType.appRule []
      churchSomeTm
      A
      Term.sort
      (Term.pi (Term.var 0)
        (Term.pi Term.sort
          (Term.pi (Term.var 0)
            (Term.pi
              (Term.pi (Term.var 3) (Term.var 2))
              (Term.var 2)))))
      BEDC.MetaCIC.church_some
      hA)
    (typed_α a)

theorem church_none_closed :
    ClosedAt 0 church_none := by
  exact closedAt_zero_at 0 church_none
    (by
      unfold church_none churchNoneTm
      apply ClosedAt.lamClosed
      · exact ClosedAt.sortClosed
      · apply ClosedAt.lamClosed
        · exact ClosedAt.sortClosed
        · apply ClosedAt.lamClosed
          · apply ClosedAt.varClosed
            exact Nat.zero_lt_succ 1
          · apply ClosedAt.lamClosed
            · apply ClosedAt.piClosed
              · apply ClosedAt.varClosed
                exact Nat.lt_succ_self 2
              · apply ClosedAt.varClosed
                exact Nat.lt_trans (Nat.lt_succ_self 2) (Nat.lt_succ_self 3)
            · apply ClosedAt.varClosed
              exact Nat.lt_trans
                (Nat.lt_succ_self 1)
                (Nat.lt_trans (Nat.lt_succ_self 2) (Nat.lt_succ_self 3)))

theorem church_some_closed :
    ClosedAt 0 church_some := by
  unfold church_some churchSomeTm
  apply ClosedAt.lamClosed
  · exact ClosedAt.sortClosed
  · apply ClosedAt.lamClosed
    · apply ClosedAt.varClosed
      exact Nat.zero_lt_succ 0
    · apply ClosedAt.lamClosed
      · exact ClosedAt.sortClosed
      · apply ClosedAt.lamClosed
        · apply ClosedAt.varClosed
          exact Nat.zero_lt_succ 2
        · apply ClosedAt.lamClosed
          · apply ClosedAt.piClosed
            · apply ClosedAt.varClosed
              exact Nat.lt_succ_self 3
            · apply ClosedAt.varClosed
              exact Nat.succ_lt_succ
                (Nat.succ_lt_succ (Nat.zero_lt_succ 2))
          · apply ClosedAt.appClosed
            · apply ClosedAt.varClosed
              exact Nat.zero_lt_succ 4
            · apply ClosedAt.varClosed
              exact Nat.succ_lt_succ
                (Nat.succ_lt_succ
                  (Nat.succ_lt_succ (Nat.zero_lt_succ 1)))

theorem church_case_option_closed :
    ClosedAt 0 church_case_option := by
  unfold church_case_option churchCaseOptionTm
  apply ClosedAt.lamClosed
  · exact ClosedAt.sortClosed
  · apply ClosedAt.lamClosed
    · exact ClosedAt.sortClosed
    · apply ClosedAt.lamClosed
      · apply ClosedAt.piClosed
        · exact ClosedAt.sortClosed
        · apply ClosedAt.piClosed
          · apply ClosedAt.varClosed
            exact Nat.zero_lt_succ 2
          · apply ClosedAt.piClosed
            · apply ClosedAt.piClosed
              · apply ClosedAt.varClosed
                exact Nat.lt_succ_self 3
              · apply ClosedAt.varClosed
                exact Nat.succ_lt_succ
                  (Nat.succ_lt_succ (Nat.zero_lt_succ 2))
            · apply ClosedAt.varClosed
              exact Nat.succ_lt_succ
                (Nat.succ_lt_succ (Nat.zero_lt_succ 2))
      · apply ClosedAt.lamClosed
        · apply ClosedAt.varClosed
          exact Nat.succ_lt_succ (Nat.zero_lt_succ 1)
        · apply ClosedAt.lamClosed
          · apply ClosedAt.piClosed
            · apply ClosedAt.varClosed
              exact Nat.lt_succ_self 3
            · apply ClosedAt.varClosed
              exact Nat.succ_lt_succ
                (Nat.succ_lt_succ
                  (Nat.succ_lt_succ (Nat.zero_lt_succ 1)))
          · apply ClosedAt.appClosed
            · apply ClosedAt.appClosed
              · apply ClosedAt.appClosed
                · apply ClosedAt.varClosed
                  exact Nat.succ_lt_succ
                    (Nat.succ_lt_succ (Nat.zero_lt_succ 2))
                · apply ClosedAt.varClosed
                  exact Nat.succ_lt_succ
                    (Nat.succ_lt_succ
                      (Nat.succ_lt_succ (Nat.zero_lt_succ 1)))
              · apply ClosedAt.varClosed
                exact Nat.lt_trans
                  (Nat.lt_succ_self 1)
                  (Nat.lt_trans
                    (Nat.lt_succ_self 2)
                    (Nat.lt_trans (Nat.lt_succ_self 3) (Nat.lt_succ_self 4)))
            · apply ClosedAt.varClosed
              exact Nat.zero_lt_succ 4

theorem hostOptionToChurch_closed
    (A : Term) (encodeα : α → Term)
    (hA : ClosedAt 0 A)
    (hencode : ∀ a, ClosedAt 0 (encodeα a))
    (x : Option α) :
    ClosedAt 0 (hostOptionToChurch A encodeα x) := by
  cases x with
  | none =>
      unfold hostOptionToChurch
      exact ClosedAt.appClosed church_none_closed hA
  | some a =>
      unfold hostOptionToChurch
      exact ClosedAt.appClosed
        (ClosedAt.appClosed church_some_closed hA)
        (hencode a)

theorem churchOptionCase_closed
    (A R opt onNone onSome : Term)
    (hA : ClosedAt 0 A) (hR : ClosedAt 0 R)
    (hopt : ClosedAt 0 opt) (hnone : ClosedAt 0 onNone)
    (hsome : ClosedAt 0 onSome) :
    ClosedAt 0 (churchOptionCaseHost A R opt onNone onSome) := by
  unfold churchOptionCaseHost
  exact ClosedAt.appClosed
    (ClosedAt.appClosed
      (ClosedAt.appClosed
        (ClosedAt.appClosed
          (ClosedAt.appClosed church_case_option_closed hA)
          hR)
        hopt)
      hnone)
    hsome

abbrev churchOptionNoneNormal : Term :=
  Term.lam Term.sort
    (Term.lam (Term.var 0)
      (Term.lam (Term.pi Term.sort (Term.var 2)) (Term.var 1)))

abbrev churchOptionSomeNormal (payload : Term) : Term :=
  Term.lam Term.sort
    (Term.lam (Term.var 0)
      (Term.lam
        (Term.pi Term.sort (Term.var 2))
        (Term.app (Term.var 0) payload)))

def decodeChurchNatNormalAsOption (t : Term) : Option Nat :=
  churchNormalToHostNat t 40

def decodeChurchBoolNormalAsOption (t : Term) : Option Bool :=
  some (churchNormalToHostBool t)

theorem normalize_hostOptionToChurch_none :
    normalizeBounded 7 (hostOptionToChurch Term.sort (fun _ : α => Term.sort) none) =
      churchOptionNoneNormal := by
  rfl

theorem normalize_hostOptionToChurch_bool_true :
    normalizeBounded 7
      (hostOptionToChurch Term.sort (fun x : Term => x) (some (hostBoolToChurch true))) =
      churchOptionSomeNormal (hostBoolToChurch true) := by
  rfl

theorem normalize_hostOptionToChurch_bool_false :
    normalizeBounded 7
      (hostOptionToChurch Term.sort (fun x : Term => x) (some (hostBoolToChurch false))) =
      churchOptionSomeNormal (hostBoolToChurch false) := by
  rfl

example
    (decodeα : Term → Option α) :
    churchNormalToHostOption decodeα churchOptionNoneNormal = none := by
  rfl

example
    (decodeα : Term → Option α) (payload : Term) :
    churchNormalToHostOption decodeα (churchOptionSomeNormal payload) =
      decodeα payload := by
  cases payload <;> rfl

example
    (decodeα : Term → Option α) :
    churchToHostOption decodeα
      (hostOptionToChurch Term.sort (fun _ : α => Term.sort) none) 7 =
      none := by
  unfold churchToHostOption
  rw [normalize_hostOptionToChurch_none]
  rfl

theorem churchOption_case_none_bool_normalize :
    normalizeBounded 14
      (churchOptionCaseHost Term.sort church_bool_ty
        (hostOptionToChurch Term.sort (fun _ : Bool => Term.sort) none)
        church_true
        (Term.lam church_bool_ty church_false)) =
      normalizeBounded 8 church_true := by
  rfl

theorem churchOption_case_some_bool_normalize :
    normalizeBounded 14
      (churchOptionCaseHost Term.sort church_bool_ty
        (hostOptionToChurch Term.sort (fun x : Term => x) (some church_false))
        church_true
        (Term.lam church_bool_ty church_false)) =
      normalizeBounded 8
        (Term.app (Term.lam church_bool_ty church_false) church_false) := by
  rfl

theorem host_none_beta :
    MetaCICTransport.Host.churchCaseOption A X
      (MetaCICTransport.Host.churchNone A) n s = n := by
  rfl

theorem host_some_beta :
    MetaCICTransport.Host.churchCaseOption A X
      (MetaCICTransport.Host.churchSome A a) n s = s a := by
  rfl

theorem hostNatToChurch_zero_normal :
    normalizeBounded 5 (hostNatToChurch 0) = hostNatToChurch 0 := by
  rfl

theorem hostNatToChurch_one_normal :
    normalizeBounded 5 (hostNatToChurch 1) =
      normalizeBounded 5 (hostNatToChurch 1) := by
  rfl

theorem hostNatToChurch_two_normal :
    normalizeBounded 5 (hostNatToChurch 2) =
      normalizeBounded 5 (hostNatToChurch 2) := by
  rfl

theorem decodeChurchNatNormal_zero :
    decodeChurchNatNormalAsOption (hostNatToChurch 0) = some 0 := by
  rfl

theorem decodeChurchNatNormal_one :
    churchToHostNat (hostNatToChurch 1) (1000 + 1 * 10) = 1 := by
  exact hostNat_roundtrip_identity 1

theorem decodeChurchNatNormal_two :
    churchToHostNat (hostNatToChurch 2) (1000 + 2 * 10) = 2 := by
  exact hostNat_roundtrip_identity 2

theorem decodeChurchNatNormalAsOption_zero :
    decodeChurchNatNormalAsOption (hostNatToChurch 0) = some 0 := by
  rfl

theorem hostBoolToChurch_true_normal :
    normalizeBounded 5 (hostBoolToChurch true) = hostBoolToChurch true := by
  rfl

theorem hostBoolToChurch_false_normal :
    normalizeBounded 5 (hostBoolToChurch false) = hostBoolToChurch false := by
  rfl

theorem decodeChurchBoolNormal_true :
    decodeChurchBoolNormalAsOption (hostBoolToChurch true) = some true := by
  rfl

theorem decodeChurchBoolNormal_false :
    decodeChurchBoolNormalAsOption (hostBoolToChurch false) = some false := by
  rfl

example :
    churchToHostOption decodeChurchBoolNormalAsOption
      (hostOptionToChurch Term.sort (fun x : Term => x) (some (hostBoolToChurch true))) 7 =
      some true := by
  unfold churchToHostOption
  rw [normalize_hostOptionToChurch_bool_true]
  rfl

example :
    churchToHostOption decodeChurchBoolNormalAsOption
      (hostOptionToChurch Term.sort (fun x : Term => x) (some (hostBoolToChurch false))) 7 =
      some false := by
  unfold churchToHostOption
  rw [normalize_hostOptionToChurch_bool_false]
  rfl

example :
    hostOptionToChurch Term.sort hostNatToChurch (none : Option Nat) =
      Term.app church_none Term.sort := rfl

example :
    hostOptionToChurch Term.sort hostNatToChurch (some 2) =
      Term.app (Term.app church_some Term.sort) (hostNatToChurch 2) := rfl

example :
    churchToHostOption decodeChurchNatNormalAsOption
      (hostOptionToChurch Term.sort hostNatToChurch (none : Option Nat)) 7 =
      none := by
  rfl

example :
    churchToHostOption decodeChurchNatNormalAsOption
      (hostOptionToChurch Term.sort (fun x : Term => x) (some (hostNatToChurch 0))) 7 =
      some 0 := by
  rfl

example :
    churchToHostOption decodeChurchBoolNormalAsOption
      (hostOptionToChurch Term.sort (fun x : Term => x) (some (hostBoolToChurch true))) 7 =
      some true := by
  rfl

example :
    churchToHostOption decodeChurchBoolNormalAsOption
      (hostOptionToChurch Term.sort (fun x : Term => x) (some (hostBoolToChurch false))) 7 =
      some false := by
  rfl

example :
    churchToHostOption decodeChurchNatNormalAsOption
      (hostOptionToChurch Term.sort (fun x : Term => x) (some (hostNatToChurch 2))) 7 =
      churchToHostOption decodeChurchNatNormalAsOption
        (hostOptionToChurch Term.sort (fun x : Term => x) (some (hostNatToChurch 2))) 7 := by
  rfl

example :
    normalizeBounded 14
      (churchOptionCaseHost Term.sort church_bool_ty
        (hostOptionToChurch Term.sort hostBoolToChurch (none : Option Bool))
        church_true
        (Term.lam church_bool_ty church_false)) =
      normalizeBounded 8 church_true := by
  exact churchOption_case_none_bool_normalize

example :
    normalizeBounded 14
      (churchOptionCaseHost Term.sort church_bool_ty
        (hostOptionToChurch Term.sort (fun x : Term => x) (some church_false))
        church_true
        (Term.lam church_bool_ty church_false)) =
      normalizeBounded 8
        (Term.app (Term.lam church_bool_ty church_false) church_false) := by
  exact churchOption_case_some_bool_normalize

end BEDC.HostBridge
