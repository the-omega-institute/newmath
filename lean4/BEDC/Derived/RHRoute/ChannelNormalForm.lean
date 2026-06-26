import BEDC.Derived.RHRoute.FinitePrimeWindow

namespace BEDC.Derived.RHRoute.ChannelNormalForm

abbrev PrimeWindow := BEDC.Derived.RHRoute.FinitePrimeWindow.PrimeWindow

structure Fingerprint (α : Type u) where
  window : PrimeWindow
  encode : α -> List Nat
  normalized : α -> Prop

def FingerprintEq (F : Fingerprint α) (x y : α) : Prop :=
  F.encode x = F.encode y

def SeparatedByWindow (F : Fingerprint α) (x y : α) : Prop :=
  F.encode x ≠ F.encode y

structure ChannelNormalForm (α : Type u) (NF : Type v) where
  fingerprint : Fingerprint α
  normalPredicate : NF -> Prop
  approxEq : α -> α -> Prop
  normalize : α -> NF
  readback : NF -> α
  sound : (x : α) -> normalPredicate (normalize x)
  readback_sound : (x : α) -> approxEq (readback (normalize x)) x
  separation :
    (x y : α) -> normalize x = normalize y -> FingerprintEq fingerprint x y

theorem normalize_eq_fingerprint_eq
    {α : Type u} {NF : Type v} (C : ChannelNormalForm α NF) {x y : α} :
    C.normalize x = C.normalize y -> FingerprintEq C.fingerprint x y := by
  intro equalNormal
  exact C.separation x y equalNormal

theorem finite_prime_fingerprint_separation
    {α : Type u} {NF : Type v} (C : ChannelNormalForm α NF) {x y : α} :
    SeparatedByWindow C.fingerprint x y -> C.normalize x ≠ C.normalize y := by
  intro separated equalNormal
  exact separated (normalize_eq_fingerprint_eq C equalNormal)

theorem finite_local_global_zero_exclusion
    {α : Type u} {NF : Type v} (C : ChannelNormalForm α NF) {x y : α} :
    SeparatedByWindow C.fingerprint x y -> C.normalize x = C.normalize y -> False := by
  intro separated
  exact finite_prime_fingerprint_separation C separated

end BEDC.Derived.RHRoute.ChannelNormalForm
