import BEDC.Derived.RealityConstrainedObjectivityUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RealityConstrainedObjectivityUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem RealityConstrainedObjectivityUp_StdBridge
    {H A I F R T P L N anchorRoute invariantRead ledgerRead publicRead : BHist} :
    UnaryHistory A →
      UnaryHistory I →
        UnaryHistory L →
          UnaryHistory N →
            Cont A I anchorRoute →
              Cont anchorRoute L invariantRead →
                Cont I L ledgerRead →
                  Cont invariantRead N publicRead →
                    SemanticNameCert
                        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row publicRead ∧ Cont A I anchorRoute ∧
                            Cont anchorRoute L invariantRead)
                        (fun row : BHist => hsame row publicRead ∧ Cont I L ledgerRead)
                        hsame ∧
                      Exists
                        (fun O : RealityConstrainedObjectivityUp =>
                          O = RealityConstrainedObjectivityUp.mk H A I F R T P L N ∧
                            UnaryHistory publicRead) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro anchorUnary invariantUnary ledgerUnary nameUnary anchorRouteCont invariantRouteCont
    ledgerRouteCont publicReadCont
  have anchorRouteUnary : UnaryHistory anchorRoute :=
    unary_cont_closed anchorUnary invariantUnary anchorRouteCont
  have invariantReadUnary : UnaryHistory invariantRead :=
    unary_cont_closed anchorRouteUnary ledgerUnary invariantRouteCont
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed invariantReadUnary nameUnary publicReadCont
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row publicRead ∧ Cont A I anchorRoute ∧ Cont anchorRoute L invariantRead)
        (fun row : BHist => hsame row publicRead ∧ Cont I L ledgerRead)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicReadUnary⟩
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' classified
        exact hsame_symm classified
      equiv_trans := by
        intro _row _row' _row'' leftClassified rightClassified
        exact hsame_trans leftClassified rightClassified
      carrier_respects_equiv := by
        intro _row _row' classified sourceRow
        cases classified
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, anchorRouteCont, invariantRouteCont⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, ledgerRouteCont⟩
  }
  exact
    ⟨cert,
      Exists.intro (RealityConstrainedObjectivityUp.mk H A I F R T P L N)
        ⟨rfl, publicReadUnary⟩⟩

end BEDC.Derived.RealityConstrainedObjectivityUp
