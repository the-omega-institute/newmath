import BEDC.Derived.RealityConstrainedSignatureFitUp.TasteGate

namespace BEDC.Derived.RealityConstrainedSignatureFitUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem RealityConstrainedSignatureFitNameCertObligations
    (R : RealityConstrainedSignatureFitUp) :
    ∃ S A M G P C H Q N : BHist,
      R = RealityConstrainedSignatureFitUp.mk S A M G P C H Q N ∧
        List.Mem S (realityConstrainedSignatureFitFields R) ∧
          List.Mem A (realityConstrainedSignatureFitFields R) ∧
            List.Mem M (realityConstrainedSignatureFitFields R) ∧
              List.Mem G (realityConstrainedSignatureFitFields R) ∧
                List.Mem P (realityConstrainedSignatureFitFields R) ∧
                  hsame S S ∧ Cont S A (append S A) := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  cases R with
  | mk S A M G P C H Q N =>
      exact
        ⟨S, A, M, G, P, C, H, Q, N, rfl,
          List.Mem.head _,
          List.Mem.tail _ (List.Mem.head _),
          List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)),
          List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))),
          List.Mem.tail _
            (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))),
          hsame_refl S,
          cont_intro rfl⟩

end BEDC.Derived.RealityConstrainedSignatureFitUp
