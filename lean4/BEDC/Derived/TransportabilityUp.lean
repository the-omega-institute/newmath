import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.TransportabilityUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

inductive TransportabilityUp : Type where
  | mk (S Tg I A D J H C P N : BHist) : TransportabilityUp

def transportabilityFields : TransportabilityUp → List BHist
  -- BEDC touchpoint anchor: BHist Cont hsame NameCert
  | TransportabilityUp.mk S Tg I A D J H C P N => [S, Tg, I, A, D, J, H, C, P, N]

theorem TransportabilityCarrier_namecert_obligations
    (x : TransportabilityUp) :
    exists S Tg I A D J H C P N route replay : BHist,
      transportabilityFields x = [S, Tg, I, A, D, J, H, C, P, N] ∧
        Cont S Tg route ∧ Cont route I replay ∧ hsame H H ∧
          Nonempty (NameCert (fun h : BHist => hsame h N) hsame) := by
  -- BEDC touchpoint anchor: BHist Cont hsame NameCert
  cases x with
  | mk S Tg I A D J H C P N =>
      refine ⟨S, Tg, I, A, D, J, H, C, P, N, append S Tg, append (append S Tg) I, ?_⟩
      constructor
      · rfl
      constructor
      · rfl
      constructor
      · rfl
      constructor
      · exact hsame_refl H
      · exact
          Nonempty.intro {
            carrier_inhabited := Exists.intro N (hsame_refl N)
            equiv_refl := by
              intro row _source
              exact hsame_refl row
            equiv_symm := by
              intro row other same
              exact hsame_symm same
            equiv_trans := by
              intro row other third sameRO sameOT
              exact hsame_trans sameRO sameOT
            carrier_respects_equiv := by
              intro row other same source
              exact hsame_trans (hsame_symm same) source
          }

end BEDC.Derived.TransportabilityUp
