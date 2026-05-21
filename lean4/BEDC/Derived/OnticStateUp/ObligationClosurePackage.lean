import BEDC.Derived.OnticStateUp.TasteGate

namespace BEDC.Derived.OnticStateUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

theorem OnticStateObligationClosurePackage (x : OnticStateUp) :
    ∃ S A K R H C P N : BHist,
      x = OnticStateUp.mk S A K R H C P N ∧
        List.Mem S (FieldFaithful.fields x) ∧
          List.Mem A (FieldFaithful.fields x) ∧
            List.Mem R (FieldFaithful.fields x) ∧
              Cont A R (append A R) ∧ hsame (append A R) (append A R) := by
  -- BEDC touchpoint anchor: BHist Cont hsame FieldFaithful
  cases x with
  | mk S A K R H C P N =>
      exact
        ⟨S, A, K, R, H, C, P, N, rfl,
          List.Mem.head _,
          List.Mem.tail _ (List.Mem.head _),
          List.Mem.tail _
            (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))),
          cont_intro rfl,
          hsame_refl (append A R)⟩

end BEDC.Derived.OnticStateUp
