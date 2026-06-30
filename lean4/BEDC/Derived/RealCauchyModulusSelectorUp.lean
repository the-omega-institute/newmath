import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RealCauchyModulusSelectorUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

inductive RealCauchyModulusSelectorUp : Type where
  | mk (M S D Q E R H P N : BHist) : RealCauchyModulusSelectorUp

def realCauchyModulusSelectorFields : RealCauchyModulusSelectorUp -> List BHist
  | RealCauchyModulusSelectorUp.mk M S D Q E R H P N =>
      [M, S, D, Q, E, R, H, append R M, P, N]

theorem RealCauchyModulusSelectorCarrier_finite_window_soundness
    (x : RealCauchyModulusSelectorUp) :
    exists M S D Q E R H C P N : BHist,
      realCauchyModulusSelectorFields x = [M, S, D, Q, E, R, H, C, P, N] ∧
        Cont R M C ∧ hsame H H ∧
          Nonempty (NameCert (fun h : BHist => hsame h N) hsame) := by
  -- BEDC touchpoint anchor: BHist Cont hsame NameCert
  cases x with
  | mk M S D Q E R H P N =>
      refine ⟨M, S, D, Q, E, R, H, append R M, P, N, ?_⟩
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

theorem RealCauchyModulusSelectorCarrier_namecert_obligations
    (x : RealCauchyModulusSelectorUp) :
    exists M S D Q E R H C P N : BHist,
      realCauchyModulusSelectorFields x = [M, S, D, Q, E, R, H, C, P, N] ∧
        Cont R M C ∧ hsame H H ∧
          Nonempty (NameCert (fun h : BHist => hsame h N) hsame) ∧
            Nonempty (NameCert (fun h : BHist => hsame h C) hsame) := by
  -- BEDC touchpoint anchor: BHist Cont hsame NameCert
  cases x with
  | mk M S D Q E R H P N =>
      refine ⟨M, S, D, Q, E, R, H, append R M, P, N, ?_⟩
      constructor
      · rfl
      constructor
      · rfl
      constructor
      · exact hsame_refl H
      constructor
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
      · exact
          Nonempty.intro {
            carrier_inhabited := Exists.intro (append R M) (hsame_refl (append R M))
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

theorem RealCauchyModulusSelectorCarrier_window_monotone
    (x : RealCauchyModulusSelectorUp) :
    exists M S D Q E R H C P N larger replayed : BHist,
      realCauchyModulusSelectorFields x = [M, S, D, Q, E, R, H, C, P, N] ∧
        Cont R M C ∧ Cont C S larger ∧ Cont larger D replayed ∧
          hsame H H ∧ Nonempty (NameCert (fun h : BHist => hsame h replayed) hsame) := by
  -- BEDC touchpoint anchor: BHist Cont hsame NameCert
  cases x with
  | mk M S D Q E R H P N =>
      refine ⟨M, S, D, Q, E, R, H, append R M, P, N, append (append R M) S,
        append (append (append R M) S) D, ?_⟩
      constructor
      · rfl
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
            carrier_inhabited :=
              Exists.intro (append (append (append R M) S) D)
                (hsame_refl (append (append (append R M) S) D))
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

theorem RealCauchyModulusSelectorCarrier_seal_factorization
    (x : RealCauchyModulusSelectorUp) :
    exists M S D Q E R H C P N sealRow : BHist,
      realCauchyModulusSelectorFields x = [M, S, D, Q, E, R, H, C, P, N] ∧
        Cont R M C ∧ Cont Q E sealRow ∧ hsame H H ∧
          Nonempty (NameCert (fun h : BHist => hsame h sealRow) hsame) := by
  -- BEDC touchpoint anchor: BHist Cont hsame NameCert
  cases x with
  | mk M S D Q E R H P N =>
      refine ⟨M, S, D, Q, E, R, H, append R M, P, N, append Q E, ?_⟩
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
            carrier_inhabited := Exists.intro (append Q E) (hsame_refl (append Q E))
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

theorem RealCauchyModulusSelectorCarrier_tail_bound
    (x : RealCauchyModulusSelectorUp) :
    exists M S D Q E R H C P N tail sealRow : BHist,
      realCauchyModulusSelectorFields x = [M, S, D, Q, E, R, H, C, P, N] ∧
        Cont R M C ∧ Cont C S tail ∧ Cont Q E sealRow ∧ hsame H H ∧
          Nonempty (NameCert (fun h : BHist => hsame h tail) hsame) ∧
            Nonempty (NameCert (fun h : BHist => hsame h sealRow) hsame) := by
  -- BEDC touchpoint anchor: BHist Cont hsame NameCert
  cases x with
  | mk M S D Q E R H P N =>
      refine ⟨M, S, D, Q, E, R, H, append R M, P, N, append (append R M) S,
        append Q E, ?_⟩
      constructor
      · rfl
      constructor
      · rfl
      constructor
      · rfl
      constructor
      · rfl
      constructor
      · exact hsame_refl H
      constructor
      · exact
          Nonempty.intro {
            carrier_inhabited :=
              Exists.intro (append (append R M) S) (hsame_refl (append (append R M) S))
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
      · exact
          Nonempty.intro {
            carrier_inhabited := Exists.intro (append Q E) (hsame_refl (append Q E))
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

theorem RealCauchyModulusSelectorCarrier_real_seal_route
    (x : RealCauchyModulusSelectorUp) :
    exists M S D Q E R H C P N tail readback sealRow route : BHist,
      realCauchyModulusSelectorFields x = [M, S, D, Q, E, R, H, C, P, N] ∧
        Cont R M C ∧ Cont C S tail ∧ Cont tail D readback ∧ Cont readback Q route ∧
          Cont Q E sealRow ∧ hsame H H ∧
            Nonempty (NameCert (fun h : BHist => hsame h route) hsame) := by
  -- BEDC touchpoint anchor: BHist Cont hsame NameCert
  cases x with
  | mk M S D Q E R H P N =>
      refine ⟨M, S, D, Q, E, R, H, append R M, P, N, append (append R M) S,
        append (append (append R M) S) D, append Q E,
        append (append (append (append R M) S) D) Q, ?_⟩
      constructor
      · rfl
      constructor
      · rfl
      constructor
      · rfl
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
            carrier_inhabited :=
              Exists.intro (append (append (append (append R M) S) D) Q)
                (hsame_refl (append (append (append (append R M) S) D) Q))
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

end BEDC.Derived.RealCauchyModulusSelectorUp
