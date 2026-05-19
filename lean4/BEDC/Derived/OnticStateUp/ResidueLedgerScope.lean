import BEDC.Derived.OnticStateUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.OnticStateUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Meta.TasteGate

theorem OnticStateResidueLedgerScope (x : OnticStateUp) :
    exists S A K R H C P N residueReplay namedResidue : BHist,
      x = OnticStateUp.mk S A K R H C P N /\
        FieldFaithful.fields x = [S, A, K, R, H, C, P, N] /\
          Cont R C residueReplay /\
            Cont residueReplay N namedResidue /\
              hsame namedResidue (append (append R C) N) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Cont hsame
  cases x with
  | mk S A K R H C P N =>
      exact
        ⟨S, A, K, R, H, C, P, N, append R C, append (append R C) N,
          rfl, rfl, rfl, rfl, hsame_refl (append (append R C) N)⟩

end BEDC.Derived.OnticStateUp
