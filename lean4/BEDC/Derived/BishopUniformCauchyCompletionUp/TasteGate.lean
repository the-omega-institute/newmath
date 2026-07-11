import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BishopUniformCauchyCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopUniformCauchyCompletionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {A W R D E S B H C P N windowRead readbackRead toleranceRead sealRead spaceRead
      theoremRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory A -> UnaryHistory W -> UnaryHistory R -> UnaryHistory D ->
      UnaryHistory E -> UnaryHistory S -> UnaryHistory B -> UnaryHistory P ->
        UnaryHistory N -> Cont A W windowRead -> Cont windowRead R readbackRead ->
          Cont readbackRead D toleranceRead -> Cont toleranceRead E sealRead ->
            Cont sealRead S spaceRead -> Cont spaceRead B theoremRead ->
              Cont theoremRead N namedRead -> PkgSig bundle P pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row A ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨
                        hsame row E ∨ hsame row S ∨ hsame row B ∨ hsame row H ∨
                          hsame row C ∨ hsame row P ∨ hsame row N ∨
                            hsame row windowRead ∨ hsame row readbackRead ∨
                              hsame row toleranceRead ∨ hsame row sealRead ∨
                                hsame row spaceRead ∨ hsame row theoremRead ∨
                                  hsame row namedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont A W windowRead ∧
                        Cont windowRead R readbackRead ∧
                          Cont readbackRead D toleranceRead ∧
                            Cont toleranceRead E sealRead ∧ Cont sealRead S spaceRead ∧
                              Cont spaceRead B theoremRead ∧
                                Cont theoremRead N namedRead ∧ PkgSig bundle P pkg)
                    hsame := by
  -- BEDC touchpoint anchor: BishopUniformCauchyCompletionUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro unaryA unaryW unaryR unaryD unaryE unaryS unaryB _unaryP unaryN windowRoute
    readbackRoute toleranceRoute sealRoute spaceRoute theoremRoute namedRoute packageP
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed unaryA unaryW windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary unaryR readbackRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed readbackUnary unaryD toleranceRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceUnary unaryE sealRoute
  have spaceUnary : UnaryHistory spaceRead :=
    unary_cont_closed sealUnary unaryS spaceRoute
  have theoremUnary : UnaryHistory theoremRead :=
    unary_cont_closed spaceUnary unaryB theoremRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed theoremUnary unaryN namedRoute
  exact {
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr source.left))))))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowRoute, readbackRoute, toleranceRoute, sealRoute, spaceRoute,
          theoremRoute, namedRoute, packageP⟩
  }

end BEDC.Derived.BishopUniformCauchyCompletionUp
