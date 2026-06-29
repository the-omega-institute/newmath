import BEDC.Derived.CanonicalTailChoiceUp.Nonescape

namespace BEDC.Derived.CanonicalTailChoiceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CanonicalTailChoiceCarrier_tail_inhabitation [AskSetup] [PackageSetup]
    {M E I T S R H C0 P N indexRead tailRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CanonicalTailChoiceCarrier M E I T S R H C0 P N bundle pkg →
      Cont M E indexRead →
        Cont indexRead T tailRead →
          Cont tailRead S sealRead →
            PkgSig bundle sealRead pkg →
              UnaryHistory indexRead ∧ UnaryHistory tailRead ∧
                UnaryHistory sealRead ∧
                  SemanticNameCert
                    (fun row : BHist => hsame row tailRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row M ∨ hsame row E ∨ hsame row I ∨ hsame row T ∨
                        hsame row S ∨ hsame row R ∨ hsame row H ∨
                          hsame row C0 ∨ hsame row P ∨ hsame row N ∨
                            hsame row indexRead ∨ hsame row tailRead ∨
                              hsame row sealRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont M E indexRead ∧
                        Cont indexRead T tailRead ∧ Cont tailRead S sealRead ∧
                          PkgSig bundle sealRead pkg)
                    hsame := by
  -- BEDC touchpoint anchor: CanonicalTailChoiceCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier indexRoute tailRoute sealRoute sealPkg
  obtain ⟨mUnary, eUnary, _iUnary, tUnary, sUnary, _rUnary, _hUnary, _c0Unary,
    _pUnary, _nUnary, _pPkg, _nPkg⟩ := carrier
  have indexUnary : UnaryHistory indexRead :=
    unary_cont_closed mUnary eUnary indexRoute
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed indexUnary tUnary tailRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sUnary sealRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row tailRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row M ∨ hsame row E ∨ hsame row I ∨ hsame row T ∨
            hsame row S ∨ hsame row R ∨ hsame row H ∨ hsame row C0 ∨
              hsame row P ∨ hsame row N ∨ hsame row indexRead ∨
                hsame row tailRead ∨ hsame row sealRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont M E indexRead ∧ Cont indexRead T tailRead ∧
            Cont tailRead S sealRead ∧ PkgSig bundle sealRead pkg)
        hsame := {
    core := {
      carrier_inhabited := ⟨tailRead, hsame_refl tailRead, tailUnary⟩
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
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      exact Or.inl source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, indexRoute, tailRoute, sealRoute, sealPkg⟩
  }
  exact ⟨indexUnary, tailUnary, sealUnary, cert⟩

end BEDC.Derived.CanonicalTailChoiceUp
