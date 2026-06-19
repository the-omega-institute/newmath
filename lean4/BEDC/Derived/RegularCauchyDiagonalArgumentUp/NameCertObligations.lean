import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyDiagonalArgumentUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyDiagonalArgumentCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {F W D R E H C P N windowRead toleranceRead diagonalRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory F ->
      UnaryHistory W ->
        UnaryHistory D ->
          UnaryHistory R ->
            UnaryHistory E ->
              UnaryHistory H ->
                UnaryHistory C ->
                  UnaryHistory P ->
                    UnaryHistory N ->
                      Cont F W windowRead ->
                        Cont windowRead D toleranceRead ->
                          Cont toleranceRead R diagonalRead ->
                            Cont diagonalRead E realRead ->
                              PkgSig bundle P pkg ->
                                PkgSig bundle N pkg ->
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row realRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row F ∨ hsame row W ∨ hsame row D ∨
                                          hsame row R ∨ hsame row E ∨ hsame row H ∨
                                            hsame row C ∨ hsame row P ∨
                                              hsame row N ∨ hsame row realRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ PkgSig bundle P pkg ∧
                                          PkgSig bundle N pkg)
                                      hsame ∧
                                    UnaryHistory windowRead ∧
                                      UnaryHistory toleranceRead ∧
                                        UnaryHistory diagonalRead ∧
                                          UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro familyUnary windowUnary dyadicUnary readbackUnary realSealUnary _transportUnary
    _replayUnary _provenanceUnary _nameUnary familyWindowRoute windowDyadicRoute
    toleranceReadbackRoute diagonalRealRoute provenancePkg namePkg
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed familyUnary windowUnary familyWindowRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed windowReadUnary dyadicUnary windowDyadicRoute
  have diagonalReadUnary : UnaryHistory diagonalRead :=
    unary_cont_closed toleranceReadUnary readbackUnary toleranceReadbackRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed diagonalReadUnary realSealUnary diagonalRealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨ hsame row E ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realRead ⟨hsame_refl realRead, realReadUnary⟩
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
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, namePkg⟩
  }
  exact ⟨cert, windowReadUnary, toleranceReadUnary, diagonalReadUnary, realReadUnary⟩

end BEDC.Derived.RegularCauchyDiagonalArgumentUp
