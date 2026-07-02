import BEDC.Derived.CauchySubnetUp

namespace BEDC.Derived.CauchySubnetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchySubnetRegSeqRatTailHandoff [AskSetup] [PackageSetup]
    {F J W R D L E H C P N windowRead tailRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySubnetCarrier F J W R D L E H C P N bundle pkg ->
      Cont W R windowRead ->
        Cont windowRead D tailRead ->
          Cont tailRead E sealRead ->
            PkgSig bundle sealRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row F ∨ hsame row J ∨ hsame row W ∨ hsame row R ∨
                      hsame row D ∨ hsame row L ∨ hsame row E ∨ hsame row sealRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont W R windowRead ∧
                      Cont windowRead D tailRead ∧ Cont tailRead E sealRead ∧
                        PkgSig bundle sealRead pkg)
                  hsame ∧
                UnaryHistory windowRead ∧ UnaryHistory tailRead ∧
                  UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: CauchySubnetCarrier BHist Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro carrier windowRoute tailRoute sealRoute sealPkg
  obtain ⟨_unaryF, _unaryJ, unaryW, unaryR, unaryD, _unaryL, unaryE, _unaryH,
    _unaryC, _unaryP, _unaryN, _filterSubnetWindow, _windowReadbackTolerance,
    _toleranceLimitSeal, _sealTransportReplay, _provenancePkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed unaryW unaryR windowRoute
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed windowUnary unaryD tailRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary unaryE sealRoute
  have sourceSeal :
      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row) sealRead := by
    exact ⟨hsame_refl sealRead, sealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row J ∨ hsame row W ∨ hsame row R ∨
              hsame row D ∨ hsame row L ∨ hsame row E ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W R windowRead ∧ Cont windowRead D tailRead ∧
              Cont tailRead E sealRead ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead sourceSeal
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
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, windowRoute, tailRoute, sealRoute, sealPkg⟩
  }
  exact ⟨cert, windowUnary, tailUnary, sealUnary⟩

end BEDC.Derived.CauchySubnetUp
