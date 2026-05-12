import BEDC.MetaCIC.TypedExamples.ChurchSum
import BEDC.MetaCIC.TypedExamples.ChurchList
import BEDC.HostBridge.MetaCICTransport
import BEDC.HostBridge.ChurchNatRoundTrip
import BEDC.HostBridge.ChurchBoolPairRoundTrip

namespace BEDC.HostBridge

open BEDC.MetaCIC

abbrev church_either_ty : Term :=
  church_either_type

abbrev church_either_case : Term :=
  church_case_either

abbrev church_list_ty : Term :=
  church_list_type

abbrev church_nil_tm : Term :=
  church_nil

abbrev church_cons_tm : Term :=
  church_cons

abbrev church_fold_tm : Term :=
  church_fold

abbrev churchEitherOf (_A _B : Term) : Term :=
  church_either_ab_type

abbrev churchInlAfterA (A : Term) : Term :=
  substitute 1 (shift 0 1 A)
    (Term.pi (Term.var 1) church_either_after_value_type)

abbrev churchInrAfterA (A : Term) : Term :=
  substitute 1 (shift 0 1 A)
    (Term.pi (Term.var 0) church_either_after_value_type)

def hostEitherToChurch
    (A B : Term) (encodeA : α → Term) (encodeB : β → Term) :
    Sum α β → Term
  | Sum.inl a => church_inl_apply A B (encodeA a)
  | Sum.inr b => church_inr_apply A B (encodeB b)

theorem hostEitherToChurch_inl_typed
    (A B : Term) (encodeA : α → Term) (encodeB : β → Term)
    (T C : Term) (a : α)
    (typedFun :
      HasType [] (Term.app (Term.app church_inl A) B)
        (Term.pi T C))
    (typedA : HasType [] (encodeA a) T) :
    HasType []
      (hostEitherToChurch A B encodeA encodeB (Sum.inl a))
      (substitute 0 (encodeA a) C) := by
  unfold hostEitherToChurch church_inl_apply
  exact HasType.appRule []
    (Term.app (Term.app church_inl A) B)
    (encodeA a)
    T
    C
    typedFun
    typedA

theorem hostEitherToChurch_inr_typed
    (A B : Term) (encodeA : α → Term) (encodeB : β → Term)
    (T C : Term) (b : β)
    (typedFun :
      HasType [] (Term.app (Term.app church_inr A) B)
        (Term.pi T C))
    (typedB : HasType [] (encodeB b) T) :
    HasType []
      (hostEitherToChurch A B encodeA encodeB (Sum.inr b))
      (substitute 0 (encodeB b) C) := by
  unfold hostEitherToChurch church_inr_apply
  exact HasType.appRule []
    (Term.app (Term.app church_inr A) B)
    (encodeB b)
    T
    C
    typedFun
    typedB

theorem church_inl_closed :
    ClosedAt 0 church_inl := by
  exact closedAt_zero_at 0 church_inl
    (hasType_closed_at_context_length church_inl_typed)

theorem church_inr_closed :
    ClosedAt 0 church_inr := by
  exact closedAt_zero_at 0 church_inr
    (hasType_closed_at_context_length church_inr_typed)

theorem church_case_either_closed :
    ClosedAt 0 church_case_either := by
  exact closedAt_zero_at 0 church_case_either
    (hasType_closed_at_context_length church_case_either_typed)

theorem hostEitherToChurch_closed
    (A B : Term) (encodeA : α → Term) (encodeB : β → Term)
    (hA : ClosedAt 0 A) (hB : ClosedAt 0 B)
    (hencodeA : ∀ a, ClosedAt 0 (encodeA a))
    (hencodeB : ∀ b, ClosedAt 0 (encodeB b))
    (x : Sum α β) :
    ClosedAt 0 (hostEitherToChurch A B encodeA encodeB x) := by
  cases x with
  | inl a =>
      unfold hostEitherToChurch church_inl_apply
      exact ClosedAt.appClosed
        (ClosedAt.appClosed
          (ClosedAt.appClosed church_inl_closed hA)
          hB)
        (hencodeA a)
  | inr b =>
      unfold hostEitherToChurch church_inr_apply
      exact ClosedAt.appClosed
        (ClosedAt.appClosed
          (ClosedAt.appClosed church_inr_closed hA)
          hB)
        (hencodeB b)

def hostListToChurch (A : Term) (encodeα : α → Term) : List α → Term
  | [] => church_nil_apply A
  | a :: as => church_cons_apply A (encodeα a)
      (hostListToChurch A encodeα as)

theorem church_cons_closed :
    ClosedAt 0 church_cons := by
  exact closedAt_zero_at 0 church_cons
    (hasType_closed_at_context_length church_cons_typed)

theorem church_fold_closed :
    ClosedAt 0 church_fold := by
  exact closedAt_zero_at 0 church_fold
    (hasType_closed_at_context_length church_fold_typed)

theorem hostListToChurch_closed
    (A : Term) (encodeα : α → Term)
    (hA : ClosedAt 0 A)
    (hencode : ∀ a, ClosedAt 0 (encodeα a))
    (xs : List α) :
    ClosedAt 0 (hostListToChurch A encodeα xs) := by
  induction xs with
  | nil =>
      unfold hostListToChurch church_nil_apply
      exact ClosedAt.appClosed church_nil_closed hA
  | cons a as ih =>
      unfold hostListToChurch church_cons_apply
      exact ClosedAt.appClosed
        (ClosedAt.appClosed
          (ClosedAt.appClosed church_cons_closed hA)
          (hencode a))
        ih

theorem hostListToChurch_nil_typed
    (A ListTy : Term) (encodeα : α → Term)
    (typedNil :
      HasType [] (church_nil_apply A) ListTy) :
    HasType [] (hostListToChurch A encodeα [])
      ListTy := by
  exact typedNil

theorem hostListToChurch_typed
    (A ListTy : Term) (encodeα : α → Term) (xs : List α)
    (typedList :
      HasType [] (hostListToChurch A encodeα xs) ListTy) :
    HasType [] (hostListToChurch A encodeα xs) ListTy := by
  exact typedList

theorem hostListToChurch_cons_head_typed
    (A : Term) (encodeα : α → Term)
    (T C : Term) (a : α)
    (typedFun :
      HasType [] (Term.app church_cons A) (Term.pi T C))
    (typedα : HasType [] (encodeα a) T) :
    HasType [] (Term.app (Term.app church_cons A) (encodeα a))
      (substitute 0 (encodeα a) C) := by
  exact HasType.appRule []
    (Term.app church_cons A)
    (encodeα a)
    T
    C
    typedFun
    typedα

def HostChurchEither (A B : Type) : Type 1 :=
  (X : Type) → (A → X) → (B → X) → X

def hostChurchInl (a : A) : HostChurchEither A B :=
  fun _ onLeft _ => onLeft a

def hostChurchInr (b : B) : HostChurchEither A B :=
  fun _ _ onRight => onRight b

def hostChurchCaseEither
    (e : HostChurchEither A B) (onLeft : A → X) (onRight : B → X) : X :=
  e X onLeft onRight

def hostEitherToChurchHost : Sum α β → HostChurchEither α β
  | Sum.inl a => hostChurchInl a
  | Sum.inr b => hostChurchInr b

def hostChurchToEither (e : HostChurchEither α β) : Sum α β :=
  hostChurchCaseEither e Sum.inl Sum.inr

theorem hostEither_roundtrip_identity (x : Sum α β) :
    hostChurchToEither (hostEitherToChurchHost x) = x := by
  cases x with
  | inl a => rfl
  | inr b => rfl

theorem hostEither_case_inl
    (a : A) (onLeft : A → X) (onRight : B → X) :
    hostChurchCaseEither (hostChurchInl (B := B) a) onLeft onRight =
      onLeft a := by
  rfl

theorem hostEither_case_inr
    (b : B) (onLeft : A → X) (onRight : B → X) :
    hostChurchCaseEither (hostChurchInr (A := A) b) onLeft onRight =
      onRight b := by
  rfl

def HostChurchList (A : Type) : Type 1 :=
  (X : Type) → (A → X → X) → X → X

def hostListToChurchHost : List A → HostChurchList A
  | [] => fun _ _ nil => nil
  | a :: as =>
      fun X cons nil => cons a (hostListToChurchHost as X cons nil)

def hostChurchListFold (xs : HostChurchList A) (cons : A → X → X) (nil : X) :
    X :=
  xs X cons nil

def hostChurchListToList (xs : HostChurchList A) : List A :=
  hostChurchListFold xs List.cons []

theorem hostList_roundtrip_identity (xs : List A) :
    hostChurchListToList (hostListToChurchHost xs) = xs := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
      change a :: hostChurchListToList (hostListToChurchHost as) = a :: as
      rw [ih]

theorem fold_consistency (list : List Nat) (f : Nat → Nat → Nat) (z : Nat) :
    hostChurchListFold (hostListToChurchHost list) f z =
      list.foldr f z := by
  induction list with
  | nil => rfl
  | cons a as ih =>
      change f a (hostChurchListFold (hostListToChurchHost as) f z) =
        f a (List.foldr f z as)
      rw [ih]

example :
    hostListToChurch Term.sort hostNatToChurch [1, 2, 3] =
      church_cons_apply Term.sort (hostNatToChurch 1)
        (church_cons_apply Term.sort (hostNatToChurch 2)
          (church_cons_apply Term.sort (hostNatToChurch 3)
            (church_nil_apply Term.sort))) := by
  rfl

example :
    hostEitherToChurch Term.sort Term.sort hostNatToChurch hostBoolToChurch
      (Sum.inl 5 : Sum Nat Bool) =
      church_inl_apply Term.sort Term.sort (hostNatToChurch 5) := by
  rfl

example :
    hostEitherToChurch Term.sort Term.sort hostNatToChurch hostBoolToChurch
      (Sum.inr true : Sum Nat Bool) =
      church_inr_apply Term.sort Term.sort (hostBoolToChurch true) := by
  rfl

example :
    hostChurchToEither
      (hostEitherToChurchHost (Sum.inl 5 : Sum Nat Bool)) =
      Sum.inl 5 := by
  rfl

example :
    hostChurchListToList (hostListToChurchHost [1, 2, 3]) = [1, 2, 3] := by
  rfl

end BEDC.HostBridge
