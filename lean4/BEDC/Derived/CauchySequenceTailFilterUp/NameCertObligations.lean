import BEDC.Derived.CauchySequenceTailFilterUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchySequenceTailFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchySequenceTailFilterCarrier [AskSetup] [PackageSetup]
    (S B F C D Q R E H K P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont UnaryHistory hsame NameCert
  UnaryHistory S ∧ UnaryHistory B ∧ UnaryHistory F ∧ UnaryHistory C ∧
    UnaryHistory D ∧ UnaryHistory Q ∧ UnaryHistory R ∧ UnaryHistory E ∧
      UnaryHistory H ∧ UnaryHistory K ∧ UnaryHistory P ∧ UnaryHistory N ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem CauchySequenceTailFilterCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {S B F C D Q R E H K P N tailRead filterRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySequenceTailFilterCarrier S B F C D Q R E H K P N bundle pkg ->
      Cont S F tailRead ->
        Cont tailRead C filterRead ->
          Cont filterRead E sealRead ->
            PkgSig bundle sealRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row S ∨ hsame row B ∨ hsame row F ∨ hsame row C ∨
                      hsame row D ∨ hsame row Q ∨ hsame row R ∨ hsame row E ∨
                        hsame row sealRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                      PkgSig bundle sealRead pkg)
                  hsame ∧
                UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier tailRoute filterRoute sealRoute sealPkg
  have sUnary : UnaryHistory S := carrier.left
  have fUnary : UnaryHistory F := carrier.right.right.left
  have cUnary : UnaryHistory C := carrier.right.right.right.left
  have eUnary : UnaryHistory E :=
    carrier.right.right.right.right.right.right.right.left
  have provenancePkg : PkgSig bundle P pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.left
  have namePkg : PkgSig bundle N pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed sUnary fUnary tailRoute
  have filterUnary : UnaryHistory filterRead :=
    unary_cont_closed tailUnary cUnary filterRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed filterUnary eUnary sealRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
                        (Or.inr source.left)))))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, provenancePkg, namePkg, sealPkg⟩
    }
  · exact sealUnary

end BEDC.Derived.CauchySequenceTailFilterUp
