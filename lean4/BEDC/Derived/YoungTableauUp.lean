import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert

namespace BEDC.Derived

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

inductive YoungTableauUp : Type where
  | mk
      (shape alphabet rowLedger columnLedger transport replayProvenance localName : BHist) :
      YoungTableauUp
  deriving DecidableEq

namespace YoungTableauUp

theorem YoungTableauCarrier_namecert_obligations (Y : YoungTableauUp) :
    ∃ shape alphabet rowLedger columnLedger transport replayProvenance localName : BHist,
      Y =
          YoungTableauUp.mk shape alphabet rowLedger columnLedger transport replayProvenance
            localName ∧
        SemanticNameCert
          (fun h : BHist => hsame h localName)
          (fun h : BHist => hsame h localName)
          (fun h : BHist => hsame h localName)
          hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert NameCert
  cases Y with
  | mk shape alphabet rowLedger columnLedger transport replayProvenance localName =>
      have sourceLocal : hsame localName localName := hsame_refl localName
      have cert :
          SemanticNameCert
            (fun h : BHist => hsame h localName)
            (fun h : BHist => hsame h localName)
            (fun h : BHist => hsame h localName)
            hsame := {
        core := {
          carrier_inhabited := Exists.intro localName sourceLocal
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
            intro row other sameRows sourceRow
            exact hsame_trans (hsame_symm sameRows) sourceRow
        }
        pattern_sound := by
          intro _row sourceRow
          exact sourceRow
        ledger_sound := by
          intro _row sourceRow
          exact sourceRow
      }
      exact
        ⟨shape, alphabet, rowLedger, columnLedger, transport, replayProvenance, localName, rfl,
          cert⟩

end YoungTableauUp

end BEDC.Derived
