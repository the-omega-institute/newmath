import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert

namespace BEDC.Derived

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

inductive SparseGridQuadratureUp : Type where
  | mk
      (multiIndex tensorRules coefficientLedger dyadicBudget streamWindows regSeqReadback
        realSeal transport replay provenance localName : BHist) :
      SparseGridQuadratureUp
  deriving DecidableEq

namespace SparseGridQuadratureUp

theorem SparseGridQuadratureCarrier_namecert_obligations (S : SparseGridQuadratureUp) :
    ∃ multiIndex tensorRules coefficientLedger dyadicBudget streamWindows regSeqReadback realSeal
        transport replay provenance localName : BHist,
      S =
          SparseGridQuadratureUp.mk multiIndex tensorRules coefficientLedger dyadicBudget
            streamWindows regSeqReadback realSeal transport replay provenance localName ∧
        SemanticNameCert
          (fun h : BHist => hsame h localName)
          (fun h : BHist => hsame h localName)
          (fun h : BHist => hsame h localName)
          hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert NameCert
  cases S with
  | mk multiIndex tensorRules coefficientLedger dyadicBudget streamWindows regSeqReadback
      realSeal transport replay provenance localName =>
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
            intro _row _other sameRows sourceRow
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
        ⟨multiIndex, tensorRules, coefficientLedger, dyadicBudget, streamWindows,
          regSeqReadback, realSeal, transport, replay, provenance, localName, rfl, cert⟩

end SparseGridQuadratureUp

end BEDC.Derived
