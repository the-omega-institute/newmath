import BEDC.Derived.PointedCompleteMetricUp
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.PointedCompleteMetricUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem PointedCompleteMetricCarrier_namecert_obligations
    (P : _root_.BEDC.Derived.PointedCompleteMetricUp) :
    ∃ M C B R H K N route nameRead : BHist,
      P = {
          metricSpace := M,
          completion := C,
          basePoint := B,
          rootedCauchy := R,
          transport := H,
          replay := K,
          nameCert := N } ∧
        Cont H K route ∧
          Cont route N nameRead ∧
            SemanticNameCert
              (fun row : BHist => hsame row nameRead)
              (fun row : BHist =>
                hsame row M ∨ hsame row C ∨ hsame row B ∨ hsame row R ∨
                  hsame row H ∨ hsame row K ∨ hsame row N ∨ hsame row nameRead)
              (fun _row : BHist => Cont H K route ∧ Cont route N nameRead)
              hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  cases P with
  | mk M C B R H K N =>
      let route : BHist := append H K
      let nameRead : BHist := append route N
      have replayRoute : Cont H K route := rfl
      have nameRoute : Cont route N nameRead := rfl
      have sourceName : (fun row : BHist => hsame row nameRead) nameRead :=
        hsame_refl nameRead
      have cert :
          SemanticNameCert
            (fun row : BHist => hsame row nameRead)
            (fun row : BHist =>
              hsame row M ∨ hsame row C ∨ hsame row B ∨ hsame row R ∨
                hsame row H ∨ hsame row K ∨ hsame row N ∨ hsame row nameRead)
            (fun _row : BHist => Cont H K route ∧ Cont route N nameRead)
            hsame := {
        core := {
          carrier_inhabited := Exists.intro nameRead sourceName
          equiv_refl := by
            intro row _source
            exact hsame_refl row
          equiv_symm := by
            intro _row _other sameRows
            exact hsame_symm sameRows
          equiv_trans := by
            intro _row _middle _other sameLeft sameRight
            exact hsame_trans sameLeft sameRight
          carrier_respects_equiv := by
            intro _row _other sameRows source
            exact hsame_trans (hsame_symm sameRows) source
        }
        pattern_sound := by
          intro _row source
          right
          right
          right
          right
          right
          right
          right
          exact source
        ledger_sound := by
          intro _row _source
          exact ⟨replayRoute, nameRoute⟩
      }
      exact ⟨M, C, B, R, H, K, N, route, nameRead, rfl, replayRoute, nameRoute, cert⟩

end BEDC.Derived.PointedCompleteMetricUp
