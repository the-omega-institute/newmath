import BEDC.Derived.CanonicalTailChoiceUp.Nonescape
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CanonicalTailChoiceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CanonicalTailChoiceCarrier_obligation_surface [AskSetup] [PackageSetup]
    {M E I T S R H C0 P N indexRead tailRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CanonicalTailChoiceCarrier M E I T S R H C0 P N bundle pkg →
      Cont M E indexRead →
        Cont indexRead T tailRead →
          Cont tailRead S sealRead →
            PkgSig bundle sealRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row M ∨ hsame row E ∨ hsame row indexRead ∨
                      hsame row T ∨ hsame row S ∨ hsame row R ∨ hsame row H ∨
                        hsame row C0 ∨ hsame row P ∨ hsame row N ∨
                          hsame row tailRead ∨ hsame row sealRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont M E indexRead ∧
                      Cont indexRead T tailRead ∧ Cont tailRead S sealRead ∧
                        PkgSig bundle sealRead pkg)
                  hsame ∧
                UnaryHistory indexRead ∧ UnaryHistory tailRead ∧
                  UnaryHistory sealRead ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier indexRoute tailRoute sealRoute sealPkg
  obtain ⟨mUnary, eUnary, _iUnary, tUnary, sUnary, _rUnary, _hUnary, _c0Unary,
    _pUnary, _nUnary, _pPkg, nPkg⟩ := carrier
  have indexUnary : UnaryHistory indexRead :=
    unary_cont_closed mUnary eUnary indexRoute
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed indexUnary tUnary tailRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row E ∨ hsame row indexRead ∨
              hsame row T ∨ hsame row S ∨ hsame row R ∨ hsame row H ∨
                hsame row C0 ∨ hsame row P ∨ hsame row N ∨ hsame row tailRead ∨
                  hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M E indexRead ∧ Cont indexRead T tailRead ∧
              Cont tailRead S sealRead ∧ PkgSig bundle sealRead pkg)
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
      repeat (first | exact source.left | apply Or.inr)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, indexRoute, tailRoute, sealRoute, sealPkg⟩
  }
  exact ⟨cert, indexUnary, tailUnary, sealUnary, nPkg⟩

end BEDC.Derived.CanonicalTailChoiceUp
