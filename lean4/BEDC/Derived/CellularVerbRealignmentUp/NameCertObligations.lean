import BEDC.Derived.CellularVerbRealignmentUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CellularVerbRealignmentUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CellularVerbRealignmentCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {B O M _H _E K _L _C P N sourceRead orbitRead comparisonRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory B →
      UnaryHistory O →
        UnaryHistory M →
          UnaryHistory K →
            UnaryHistory N →
              Cont B O sourceRead →
                Cont sourceRead M orbitRead →
                  Cont orbitRead K comparisonRead →
                    Cont comparisonRead N namedRead →
                      PkgSig bundle P pkg →
                        PkgSig bundle namedRead pkg →
                          SemanticNameCert
                              (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row B ∨ hsame row O ∨ hsame row M ∨
                                  hsame row K ∨ hsame row N ∨ hsame row sourceRead ∨
                                    hsame row orbitRead ∨ hsame row comparisonRead ∨
                                      hsame row namedRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont B O sourceRead ∧
                                  Cont sourceRead M orbitRead ∧
                                    Cont orbitRead K comparisonRead ∧
                                      Cont comparisonRead N namedRead ∧
                                        PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg)
                              hsame ∧
                            UnaryHistory sourceRead ∧
                              UnaryHistory orbitRead ∧
                                UnaryHistory comparisonRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro bUnary oUnary mUnary kUnary nUnary sourceRoute orbitRoute comparisonRoute
    nameRoute provenancePkg namedPkg
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed bUnary oUnary sourceRoute
  have orbitUnary : UnaryHistory orbitRead :=
    unary_cont_closed sourceUnary mUnary orbitRoute
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed orbitUnary kUnary comparisonRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed comparisonUnary nUnary nameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row O ∨ hsame row M ∨ hsame row K ∨ hsame row N ∨
              hsame row sourceRead ∨ hsame row orbitRead ∨ hsame row comparisonRead ∨
                hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont B O sourceRead ∧ Cont sourceRead M orbitRead ∧
              Cont orbitRead K comparisonRead ∧ Cont comparisonRead N namedRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := ⟨namedRead, hsame_refl namedRead, namedUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sourceRoute, orbitRoute, comparisonRoute, nameRoute,
          provenancePkg, namedPkg⟩
  }
  exact ⟨cert, sourceUnary, orbitUnary, comparisonUnary, namedUnary⟩

end BEDC.Derived.CellularVerbRealignmentUp
