import BEDC.Derived.RealClassifierUp

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealClassifierCommonWindowTotality [AskSetup] [PackageSetup]
    {X Y SX SY RX RY W D C E H K P N leftReg leftRead windowRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealClassifierCarrier X Y SX SY RX RY W D C E H K P N bundle pkg ->
      Cont SX RX leftReg ->
        Cont leftReg D leftRead ->
          Cont W D windowRead ->
            Cont windowRead E publicRead ->
              PkgSig bundle publicRead pkg ->
                SemanticNameCert
                    (fun row : BHist =>
                      (hsame row leftRead ∨ hsame row publicRead) ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row SX ∨ hsame row RX ∨ hsame row W ∨ hsame row D ∨
                        hsame row E ∨ hsame row leftRead ∨ hsame row windowRead ∨
                          hsame row publicRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont SX RX leftReg ∧
                        Cont leftReg D leftRead ∧ Cont W D windowRead ∧
                          Cont windowRead E publicRead ∧ PkgSig bundle publicRead pkg)
                    hsame ∧
                  UnaryHistory leftRead ∧ UnaryHistory windowRead ∧
                    UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier leftRegRoute leftRoute windowRoute publicRoute publicPkg
  obtain ⟨_xUnary, _yUnary, sxUnary, _syUnary, rxUnary, _ryUnary, wUnary,
    dUnary, _cUnary, eUnary, _hUnary, _kUnary, _pUnary, _nUnary, _sealPkg⟩ :=
    carrier
  have leftRegUnary : UnaryHistory leftReg :=
    unary_cont_closed sxUnary rxUnary leftRegRoute
  have leftReadUnary : UnaryHistory leftRead :=
    unary_cont_closed leftRegUnary dUnary leftRoute
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary dUnary windowRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed windowReadUnary eUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row leftRead ∨ hsame row publicRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row SX ∨ hsame row RX ∨ hsame row W ∨ hsame row D ∨
              hsame row E ∨ hsame row leftRead ∨ hsame row windowRead ∨
                hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont SX RX leftReg ∧ Cont leftReg D leftRead ∧
              Cont W D windowRead ∧ Cont windowRead E publicRead ∧
                PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro leftRead ⟨Or.inl (hsame_refl leftRead), leftReadUnary⟩
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
        constructor
        · cases source.left with
          | inl leftSame =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) leftSame)
          | inr publicSame =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) publicSame)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl leftSame =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl leftSame)))))
      | inr publicSame =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr (Or.inr (Or.inr publicSame))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, leftRegRoute, leftRoute, windowRoute, publicRoute, publicPkg⟩
  }
  exact ⟨cert, leftReadUnary, windowReadUnary, publicReadUnary⟩

end BEDC.Derived
