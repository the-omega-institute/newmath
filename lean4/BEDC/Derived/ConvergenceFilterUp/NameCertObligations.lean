import BEDC.Derived.ConvergenceFilterUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ConvergenceFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ConvergenceFilterNamecertObligations [AskSetup] [PackageSetup]
    {F Nb x W R E H C P N baseRead neighbourhoodRead windowRead sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.convergenceFilterRows
        (BEDC.Derived.ConvergenceFilterUp.mk F Nb x W R E H C P N) =
        [F, Nb, x, W, R, E, H, C, P, N] →
      UnaryHistory F →
        UnaryHistory Nb →
          UnaryHistory x →
            UnaryHistory W →
              UnaryHistory R →
                UnaryHistory E →
                  UnaryHistory N →
                    Cont F Nb baseRead →
                      Cont baseRead x neighbourhoodRead →
                        Cont W R windowRead →
                          Cont windowRead E sealRead →
                            Cont sealRead N namedRead →
                              PkgSig bundle P pkg →
                                PkgSig bundle namedRead pkg →
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row namedRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row F ∨ hsame row Nb ∨ hsame row x ∨
                                          hsame row W ∨ hsame row R ∨ hsame row E ∨
                                            hsame row H ∨ hsame row C ∨ hsame row P ∨
                                              hsame row N ∨ hsame row namedRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont F Nb baseRead ∧
                                          Cont baseRead x neighbourhoodRead ∧
                                            Cont W R windowRead ∧ Cont windowRead E sealRead ∧
                                              Cont sealRead N namedRead ∧
                                                PkgSig bundle P pkg ∧
                                                  PkgSig bundle namedRead pkg)
                                      hsame ∧ UnaryHistory baseRead ∧
                                    UnaryHistory neighbourhoodRead ∧ UnaryHistory windowRead ∧
                                      UnaryHistory sealRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro _rows fUnary nbUnary xUnary wUnary rUnary eUnary nUnary baseRoute
    neighbourhoodRoute windowRoute sealRoute namedRoute provenancePkg namedPkg
  have baseUnary : UnaryHistory baseRead :=
    unary_cont_closed fUnary nbUnary baseRoute
  have neighbourhoodUnary : UnaryHistory neighbourhoodRead :=
    unary_cont_closed baseUnary xUnary neighbourhoodRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary rUnary windowRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed windowUnary eUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row Nb ∨ hsame row x ∨ hsame row W ∨ hsame row R ∨
              hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont F Nb baseRead ∧ Cont baseRead x neighbourhoodRead ∧
              Cont W R windowRead ∧ Cont windowRead E sealRead ∧ Cont sealRead N namedRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg)
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, baseRoute, neighbourhoodRoute, windowRoute, sealRoute, namedRoute,
          provenancePkg, namedPkg⟩
  }
  exact ⟨cert, baseUnary, neighbourhoodUnary, windowUnary, sealUnary, namedUnary⟩

end BEDC.Derived.ConvergenceFilterUp
