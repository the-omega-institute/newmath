import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LeibnizSeriesTestUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LeibnizSeriesTestCarrier [AskSetup] [PackageSetup]
    (S Sigma M T Q R E H C P N : BHist) (bundle : ProbeBundle ProbeName)
    (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory S ∧
    UnaryHistory Sigma ∧
      UnaryHistory M ∧
        UnaryHistory T ∧
          UnaryHistory Q ∧
            UnaryHistory R ∧
              UnaryHistory E ∧
                UnaryHistory H ∧
                  UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg

theorem LeibnizSeriesTestNameCertObligations [AskSetup] [PackageSetup]
    {S Sigma M T Q R E H C P N tailRead regRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LeibnizSeriesTestCarrier S Sigma M T Q R E H C P N bundle pkg →
      Cont T Q tailRead →
        Cont tailRead R regRead →
          Cont regRead E sealRead →
            PkgSig bundle sealRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row S ∨ hsame row Sigma ∨ hsame row M ∨ hsame row T ∨
                      hsame row Q ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
                        hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row sealRead)
                  (fun row : BHist => UnaryHistory row ∧ PkgSig bundle sealRead pkg)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier tailCont regCont sealCont sealPkg
  have tUnary : UnaryHistory T := carrier.right.right.right.left
  have qUnary : UnaryHistory Q := carrier.right.right.right.right.left
  have rUnary : UnaryHistory R := carrier.right.right.right.right.right.left
  have eUnary : UnaryHistory E := carrier.right.right.right.right.right.right.left
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed tUnary qUnary tailCont
  have regUnary : UnaryHistory regRead :=
    unary_cont_closed tailUnary rUnary regCont
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regUnary eUnary sealCont
  exact {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
                          (Or.inr
                            (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sealPkg⟩
  }

end BEDC.Derived.LeibnizSeriesTestUp
