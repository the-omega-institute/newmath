import BEDC.Derived.RealClassifierUp
import BEDC.FKernel.Cont

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealClassifierTheoremCheckReadbackRoute [AskSetup] [PackageSetup]
    {X Y SX SY RX RY W D C E H K P N regLeft regRight windowRead classifierRead sealRead
      targetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealClassifierCarrier X Y SX SY RX RY W D C E H K P N bundle pkg ->
      Cont SX RX regLeft ->
        Cont SY RY regRight ->
          Cont W D windowRead ->
            Cont windowRead C classifierRead ->
              Cont classifierRead E sealRead ->
                Cont sealRead K targetRead ->
                  PkgSig bundle targetRead pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row targetRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row X ∨ hsame row Y ∨ hsame row SX ∨ hsame row SY ∨
                            hsame row RX ∨ hsame row RY ∨ hsame row W ∨ hsame row D ∨
                              hsame row C ∨ hsame row E ∨ hsame row H ∨ hsame row K ∨
                                hsame row P ∨ hsame row N ∨ hsame row regLeft ∨
                                  hsame row regRight ∨ hsame row windowRead ∨
                                    hsame row classifierRead ∨ hsame row sealRead ∨
                                      hsame row targetRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont SX RX regLeft ∧ Cont SY RY regRight ∧
                            Cont W D windowRead ∧ Cont windowRead C classifierRead ∧
                              Cont classifierRead E sealRead ∧ Cont sealRead K targetRead ∧
                                PkgSig bundle targetRead pkg)
                        hsame ∧
                      UnaryHistory regLeft ∧ UnaryHistory regRight ∧
                        UnaryHistory windowRead ∧ UnaryHistory classifierRead ∧
                          UnaryHistory sealRead ∧ UnaryHistory targetRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier leftRoute rightRoute windowRoute classifierRoute sealRoute targetRoute targetPkg
  obtain ⟨_xUnary, _yUnary, sxUnary, syUnary, rxUnary, ryUnary, wUnary, dUnary,
    cUnary, eUnary, _hUnary, kUnary, _pUnary, _nUnary, _sealPkg⟩ := carrier
  have regLeftUnary : UnaryHistory regLeft :=
    unary_cont_closed sxUnary rxUnary leftRoute
  have regRightUnary : UnaryHistory regRight :=
    unary_cont_closed syUnary ryUnary rightRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary dUnary windowRoute
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed windowUnary cUnary classifierRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed classifierUnary eUnary sealRoute
  have targetUnary : UnaryHistory targetRead :=
    unary_cont_closed sealUnary kUnary targetRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row targetRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Y ∨ hsame row SX ∨ hsame row SY ∨ hsame row RX ∨
              hsame row RY ∨ hsame row W ∨ hsame row D ∨ hsame row C ∨ hsame row E ∨
                hsame row H ∨ hsame row K ∨ hsame row P ∨ hsame row N ∨
                  hsame row regLeft ∨ hsame row regRight ∨ hsame row windowRead ∨
                    hsame row classifierRead ∨ hsame row sealRead ∨ hsame row targetRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont SX RX regLeft ∧ Cont SY RY regRight ∧
              Cont W D windowRead ∧ Cont windowRead C classifierRead ∧
                Cont classifierRead E sealRead ∧ Cont sealRead K targetRead ∧
                  PkgSig bundle targetRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro targetRead ⟨hsame_refl targetRead, targetUnary⟩
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
      repeat (first | exact source.left | apply Or.inr)
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, leftRoute, rightRoute, windowRoute, classifierRoute, sealRoute,
          targetRoute, targetPkg⟩
  }
  exact
    ⟨cert, regLeftUnary, regRightUnary, windowUnary, classifierUnary, sealUnary, targetUnary⟩

end BEDC.Derived
