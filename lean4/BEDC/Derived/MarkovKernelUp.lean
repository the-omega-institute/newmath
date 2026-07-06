import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MarkovKernelUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

inductive MarkovKernelUp : Type where
  | mk (S T AT k N E H P L : BHist) : MarkovKernelUp

def markovKernelFields : MarkovKernelUp -> List BHist
  | MarkovKernelUp.mk S T AT k N E H P L =>
      [S, T, AT, k, N, E, H, append S k, P, L]

theorem MarkovKernelCarrier_namecert_obligations (x : MarkovKernelUp) :
    exists S T AT k N E H C P L : BHist,
      markovKernelFields x = [S, T, AT, k, N, E, H, C, P, L] ∧
        hsame H H ∧ Cont S k C ∧
          Nonempty (NameCert (fun h : BHist => hsame h L) hsame) := by
  -- BEDC touchpoint anchor: BHist Cont hsame NameCert
  cases x with
  | mk S T AT k N E H P L =>
      refine ⟨S, T, AT, k, N, E, H, append S k, P, L, ?_⟩
      constructor
      · rfl
      constructor
      · exact hsame_refl H
      constructor
      · rfl
      · exact
          Nonempty.intro {
            carrier_inhabited := Exists.intro L (hsame_refl L)
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

theorem MarkovKernel_transition_distribution_handoff (x : MarkovKernelUp) :
    exists S T AT k N E H C P L : BHist,
      markovKernelFields x = [S, T, AT, k, N, E, H, C, P, L] ∧
        Cont S k C ∧ hsame C (append S k) ∧
          Nonempty (NameCert (fun h : BHist => hsame h L) hsame) := by
  -- BEDC touchpoint anchor: BHist Cont hsame NameCert
  cases x with
  | mk S T AT k N E H P L =>
      refine ⟨S, T, AT, k, N, E, H, append S k, P, L, ?_⟩
      constructor
      · rfl
      constructor
      · rfl
      constructor
      · exact hsame_refl (append S k)
      · exact
          Nonempty.intro {
            carrier_inhabited := Exists.intro L (hsame_refl L)
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

end BEDC.Derived.MarkovKernelUp
