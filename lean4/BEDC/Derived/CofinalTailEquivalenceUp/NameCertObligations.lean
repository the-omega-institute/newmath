import BEDC.Derived.CofinalTailEquivalenceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CofinalTailEquivalenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CofinalTailEquivalence_namecert_obligations [AskSetup] [PackageSetup]
    {R0 R1 W Q D A H C P N routeRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    cofinalTailEquivalenceFields (CofinalTailEquivalenceUp.mk R0 R1 W Q D A H C P N) =
        [R0, R1, W, Q, D, A, H, C, P, N] →
      UnaryHistory R0 →
        UnaryHistory R1 →
          UnaryHistory W →
            UnaryHistory Q →
              UnaryHistory D →
                UnaryHistory A →
                  UnaryHistory N →
                    Cont R0 W routeRead →
                      Cont routeRead Q sealRead →
                        PkgSig bundle N pkg →
                          PkgSig bundle sealRead pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row R0 ∨ hsame row R1 ∨ hsame row W ∨
                                    hsame row Q ∨ hsame row D ∨ hsame row A ∨
                                      hsame row sealRead)
                                (fun _row : BHist =>
                                  PkgSig bundle sealRead pkg ∧ PkgSig bundle N pkg)
                                hsame ∧
                              UnaryHistory routeRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro fieldProjection unaryR0 _unaryR1 unaryW unaryQ _unaryD _unaryA _unaryN
    routeCont sealCont namePkg sealPkg
  have projectedFields :
      cofinalTailEquivalenceFields (CofinalTailEquivalenceUp.mk R0 R1 W Q D A H C P N) =
        [R0, R1, W, Q, D, A, H, C, P, N] :=
    fieldProjection
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed unaryR0 unaryW routeCont
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed routeUnary unaryQ sealCont
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R0 ∨ hsame row R1 ∨ hsame row W ∨ hsame row Q ∨
              hsame row D ∨ hsame row A ∨ hsame row sealRead)
          (fun row : BHist => PkgSig bundle sealRead pkg ∧ PkgSig bundle N pkg)
          hsame := {
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
      cases projectedFields
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row _source
      exact ⟨sealPkg, namePkg⟩
  }
  exact ⟨cert, routeUnary, sealUnary⟩

end BEDC.Derived.CofinalTailEquivalenceUp
