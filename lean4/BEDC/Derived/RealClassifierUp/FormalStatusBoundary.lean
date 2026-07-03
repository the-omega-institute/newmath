import BEDC.Derived.RealClassifierUp

namespace BEDC.Derived.RealClassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealClassifierFormalStatusBoundary [AskSetup] [PackageSetup]
    {X Y SX SY RX RY W D C E H K P N windowRead classifierRead exactRead
      statusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealClassifierCarrier X Y SX SY RX RY W D C E H K P N bundle pkg ->
      Cont W D windowRead ->
        Cont windowRead E classifierRead ->
          Cont classifierRead N exactRead ->
            Cont exactRead P statusRead ->
              PkgSig bundle statusRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row statusRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row X ∨ hsame row Y ∨ hsame row SX ∨ hsame row SY ∨
                        hsame row RX ∨ hsame row RY ∨ hsame row W ∨ hsame row D ∨
                          hsame row C ∨ hsame row E ∨ hsame row H ∨ hsame row K ∨
                            hsame row P ∨ hsame row N ∨ hsame row exactRead ∨
                              hsame row statusRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont W D windowRead ∧
                        Cont windowRead E classifierRead ∧
                          Cont classifierRead N exactRead ∧
                            Cont exactRead P statusRead ∧ PkgSig bundle statusRead pkg)
                    hsame ∧
                  UnaryHistory exactRead ∧ UnaryHistory statusRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont hsame SemanticNameCert UnaryHistory
  intro carrier windowRoute classifierRoute exactRoute statusRoute statusPkg
  obtain ⟨_xUnary, _yUnary, _sxUnary, _syUnary, _rxUnary, _ryUnary, wUnary,
    dUnary, _cUnary, eUnary, _hUnary, _kUnary, pUnary, nUnary, _sealPkg⟩ :=
    carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary dUnary windowRoute
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed windowUnary eUnary classifierRoute
  have exactUnary : UnaryHistory exactRead :=
    unary_cont_closed classifierUnary nUnary exactRoute
  have statusUnary : UnaryHistory statusRead :=
    unary_cont_closed exactUnary pUnary statusRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row statusRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Y ∨ hsame row SX ∨ hsame row SY ∨
              hsame row RX ∨ hsame row RY ∨ hsame row W ∨ hsame row D ∨
                hsame row C ∨ hsame row E ∨ hsame row H ∨ hsame row K ∨
                  hsame row P ∨ hsame row N ∨ hsame row exactRead ∨
                    hsame row statusRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W D windowRead ∧
              Cont windowRead E classifierRead ∧ Cont classifierRead N exactRead ∧
                Cont exactRead P statusRead ∧ PkgSig bundle statusRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro statusRead
        ⟨hsame_refl statusRead, statusUnary⟩
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
        ⟨source.right, windowRoute, classifierRoute, exactRoute, statusRoute, statusPkg⟩
  }
  exact ⟨cert, exactUnary, statusUnary⟩

end BEDC.Derived.RealClassifierUp
