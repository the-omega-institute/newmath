import BEDC.Derived.RealDiagonalNonSurjectionUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealDiagonalNonSurjectionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealDiagonalNonSurjectionNameCertObligations [AskSetup] [PackageSetup]
    {E W B F R S H C P N diagonalRead sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory E ->
      UnaryHistory W ->
        UnaryHistory B ->
          UnaryHistory F ->
            UnaryHistory R ->
              UnaryHistory S ->
                UnaryHistory H ->
                  UnaryHistory C ->
                    UnaryHistory P ->
                      UnaryHistory N ->
                        PkgSig bundle P pkg ->
                          PkgSig bundle N pkg ->
                            Cont E W diagonalRead ->
                              Cont diagonalRead F R ->
                                Cont R S sealRead ->
                                  Cont sealRead N namedRead ->
                                    PkgSig bundle namedRead pkg ->
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row namedRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row E ∨ hsame row W ∨
                                              hsame row B ∨ hsame row F ∨
                                                hsame row R ∨ hsame row S ∨
                                                  hsame row H ∨ hsame row C ∨
                                                    hsame row P ∨ hsame row N ∨
                                                      hsame row diagonalRead ∨
                                                        hsame row sealRead ∨
                                                          hsame row namedRead)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧ Cont E W diagonalRead ∧
                                              Cont diagonalRead F R ∧ Cont R S sealRead ∧
                                                Cont sealRead N namedRead ∧
                                                  PkgSig bundle P pkg ∧
                                                    PkgSig bundle namedRead pkg)
                                          hsame ∧ UnaryHistory diagonalRead ∧
                                        UnaryHistory sealRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro eUnary wUnary _bUnary fUnary rUnary sUnary _hUnary _cUnary _pUnary nUnary
    provenancePkg _localNamePkg diagonalRoute readbackRoute sealRoute namedRoute namedPkg
  have diagonalUnary : UnaryHistory diagonalRead :=
    unary_cont_closed eUnary wUnary diagonalRoute
  have readbackUnary : UnaryHistory R :=
    unary_cont_closed diagonalUnary fUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary sUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row E ∨ hsame row W ∨ hsame row B ∨ hsame row F ∨ hsame row R ∨
              hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row diagonalRead ∨ hsame row sealRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont E W diagonalRead ∧ Cont diagonalRead F R ∧
              Cont R S sealRead ∧ Cont sealRead N namedRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, diagonalRoute, readbackRoute, sealRoute, namedRoute,
          provenancePkg, namedPkg⟩
  }
  exact ⟨cert, diagonalUnary, sealUnary, namedUnary⟩

end BEDC.Derived.RealDiagonalNonSurjectionUp
