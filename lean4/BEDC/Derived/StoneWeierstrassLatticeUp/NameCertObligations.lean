import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.StoneWeierstrassLatticeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem StoneWeierstrassLatticeNameCertObligations [AskSetup] [PackageSetup]
    {K F A S B R H C P N approxRead sealedRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory K → UnaryHistory F → UnaryHistory A → UnaryHistory S →
      UnaryHistory B → UnaryHistory R → UnaryHistory H → UnaryHistory C →
        UnaryHistory P → UnaryHistory N → Cont K F approxRead →
          Cont approxRead A S → Cont S B sealedRead → Cont sealedRead R H →
            Cont H C namedRead → PkgSig bundle P pkg → PkgSig bundle N pkg →
              SemanticNameCert
                (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row K ∨ hsame row F ∨ hsame row A ∨ hsame row S ∨
                    hsame row B ∨ hsame row R ∨ hsame row H ∨ hsame row C ∨
                      hsame row P ∨ hsame row N ∨ hsame row approxRead ∨
                        hsame row sealedRead ∨ hsame row namedRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont K F approxRead ∧ Cont approxRead A S ∧
                    Cont S B sealedRead ∧ Cont sealedRead R H ∧ Cont H C namedRead ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                hsame ∧
                UnaryHistory approxRead ∧ UnaryHistory sealedRead ∧
                  UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro kUnary fUnary aUnary sUnary bUnary rUnary _hUnary cUnary _pUnary _nUnary
    approxRoute latticeRoute sealedRoute realRoute namedRoute provenancePkg namePkg
  have approxUnary : UnaryHistory approxRead :=
    unary_cont_closed kUnary fUnary approxRoute
  have sealedUnary : UnaryHistory sealedRead :=
    unary_cont_closed sUnary bUnary sealedRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed (unary_cont_closed sealedUnary rUnary realRoute) cUnary namedRoute
  constructor
  · exact {
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
        exact Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr source.left)))))))))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, approxRoute, latticeRoute, sealedRoute, realRoute, namedRoute,
            provenancePkg, namePkg⟩
    }
  · exact ⟨approxUnary, sealedUnary, namedUnary⟩

end BEDC.Derived.StoneWeierstrassLatticeUp
