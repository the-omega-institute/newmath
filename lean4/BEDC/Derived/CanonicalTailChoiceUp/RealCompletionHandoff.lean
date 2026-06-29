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

theorem CanonicalTailChoiceCarrier_real_completion_handoff [AskSetup] [PackageSetup]
    {M E I T S R H C0 P N sealRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CanonicalTailChoiceCarrier M E I T S R H C0 P N bundle pkg →
      Cont T S sealRead →
        Cont sealRead R boundaryRead →
          PkgSig bundle boundaryRead pkg →
            SemanticNameCert
              (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row M ∨ hsame row E ∨ hsame row I ∨ hsame row T ∨
                  hsame row S ∨ hsame row R ∨ hsame row boundaryRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont T S sealRead ∧
                  Cont sealRead R boundaryRead ∧ PkgSig bundle boundaryRead pkg)
              hsame ∧ UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier sealRoute boundaryRoute boundaryPkg
  obtain ⟨_mUnary, _eUnary, _iUnary, tUnary, sUnary, rUnary, _hUnary, _c0Unary,
    _pUnary, _nUnary, _pPkg, _nPkg⟩ := carrier
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed tUnary sUnary sealRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed sealUnary rUnary boundaryRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row E ∨ hsame row I ∨ hsame row T ∨
              hsame row S ∨ hsame row R ∨ hsame row boundaryRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont T S sealRead ∧ Cont sealRead R boundaryRead ∧
              PkgSig bundle boundaryRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro boundaryRead ⟨hsame_refl boundaryRead, boundaryUnary⟩
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
      exact ⟨source.right, sealRoute, boundaryRoute, boundaryPkg⟩
  }
  exact ⟨cert, boundaryUnary⟩

end BEDC.Derived.CanonicalTailChoiceUp
