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

theorem CauchyTailModulusSealThresholdReadback [AskSetup] [PackageSetup]
    {M F X tau D W0 W1 Q0 Q1 E H C P N thresholdRead windowRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory M ->
      UnaryHistory F ->
        UnaryHistory D ->
          UnaryHistory E ->
            Cont M F thresholdRead ->
              Cont thresholdRead D windowRead ->
                Cont windowRead E sealRead ->
                  PkgSig bundle sealRead pkg ->
                    cauchyTailModulusSealFields
                        (CauchyTailModulusSealUp.mk M F X tau D W0 W1 Q0 Q1 E H C P N) =
                      [M, F, X, tau, D, W0, W1, Q0, Q1, E, H, C, P, N] ∧
                      UnaryHistory thresholdRead ∧ UnaryHistory windowRead ∧
                        UnaryHistory sealRead ∧ Cont M F thresholdRead ∧
                          Cont thresholdRead D windowRead ∧ Cont windowRead E sealRead ∧
                            PkgSig bundle sealRead pkg ∧
                              SemanticNameCert
                                (fun row : BHist =>
                                  hsame row sealRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row thresholdRead ∨ hsame row windowRead ∨
                                    hsame row sealRead)
                                (fun row : BHist =>
                                  hsame row sealRead ∧ PkgSig bundle sealRead pkg)
                                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont hsame SemanticNameCert UnaryHistory
  intro unaryM unaryF unaryD unaryE thresholdRoute windowRoute sealRoute sealPkg
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed unaryM unaryF thresholdRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed thresholdUnary unaryD windowRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed windowUnary unaryE sealRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row thresholdRead ∨ hsame row windowRead ∨ hsame row sealRead)
        (fun row : BHist => hsame row sealRead ∧ PkgSig bundle sealRead pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.left, sealPkg⟩
  }
  exact
    ⟨rfl, thresholdUnary, windowUnary, sealUnary, thresholdRoute, windowRoute, sealRoute,
      sealPkg, cert⟩

end BEDC.Derived.CauchyTailModulusSealUp
