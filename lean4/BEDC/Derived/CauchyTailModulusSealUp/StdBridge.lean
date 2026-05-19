import BEDC.Derived.CauchyTailModulusSealUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyTailModulusSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyTailModulusSealUp_StdBridge [AskSetup] [PackageSetup]
    {M F X tau D W0 W1 Q0 Q1 E H C P N thresholdRead dyadicRead windowRead readbackRead
      sealRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory M ->
      UnaryHistory F ->
        UnaryHistory X ->
          UnaryHistory tau ->
            UnaryHistory D ->
              UnaryHistory W0 ->
                UnaryHistory W1 ->
                  UnaryHistory Q0 ->
                    UnaryHistory Q1 ->
                      UnaryHistory E ->
                        Cont M F thresholdRead ->
                          Cont thresholdRead tau dyadicRead ->
                            Cont dyadicRead D windowRead ->
                              Cont windowRead W0 readbackRead ->
                                Cont readbackRead Q0 sealRead ->
                                  Cont sealRead E publicRead ->
                                    PkgSig bundle publicRead pkg ->
                                      cauchyTailModulusSealFields
                                          (CauchyTailModulusSealUp.mk M F X tau D W0 W1 Q0
                                            Q1 E H C P N) =
                                        [M, F, X, tau, D, W0, W1, Q0, Q1, E, H, C, P, N] ∧
                                        SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row publicRead ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row thresholdRead ∨
                                                hsame row dyadicRead ∨
                                                  hsame row windowRead ∨
                                                    hsame row readbackRead ∨
                                                      hsame row sealRead ∨
                                                        hsame row publicRead)
                                            (fun row : BHist =>
                                              hsame row publicRead ∧
                                                PkgSig bundle publicRead pkg)
                                            hsame ∧
                                          UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro unaryM unaryF _unaryX unaryTau unaryD unaryW0 _unaryW1 unaryQ0 _unaryQ1 unaryE
    thresholdRoute dyadicRoute windowRoute readbackRoute sealRoute publicRoute publicPkg
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed unaryM unaryF thresholdRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed thresholdUnary unaryTau dyadicRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed dyadicUnary unaryD windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary unaryW0 readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary unaryQ0 sealRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sealUnary unaryE publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row thresholdRead ∨ hsame row dyadicRead ∨ hsame row windowRead ∨
              hsame row readbackRead ∨ hsame row sealRead ∨ hsame row publicRead)
          (fun row : BHist => hsame row publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, publicPkg⟩
  }
  exact ⟨rfl, cert, publicUnary⟩

end BEDC.Derived.CauchyTailModulusSealUp
