import BEDC.Derived.OnticStateUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.OnticStateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.Meta.TasteGate

theorem OnticStateUp_StdBridge [AskSetup] [PackageSetup]
    {S A K R H C P N publicRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont S A publicRead →
      Cont publicRead R namedRead →
        PkgSig bundle N pkg →
          SemanticNameCert
              (fun row : BHist =>
                hsame row N ∧
                  FieldFaithful.fields (OnticStateUp.mk S A K R H C P N) =
                    [S, A, K, R, H, C, P, N])
              (fun row : BHist =>
                hsame row S ∨ hsame row A ∨ hsame row R ∨ hsame row N ∨
                  (Cont S A publicRead ∧ Cont publicRead R namedRead))
              (fun row : BHist => hsame row N ∧ PkgSig bundle N pkg)
              hsame ∧
            FieldFaithful.fields (OnticStateUp.mk S A K R H C P N) =
              [S, A, K, R, H, C, P, N] ∧
              Cont S A publicRead ∧ Cont publicRead R namedRead ∧
                PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert FieldFaithful hsame
  intro sourceAccess publicNamed pkgSig
  have fields :
      FieldFaithful.fields (OnticStateUp.mk S A K R H C P N) =
        [S, A, K, R, H, C, P, N] := by
    rfl
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row N ∧
              FieldFaithful.fields (OnticStateUp.mk S A K R H C P N) =
                [S, A, K, R, H, C, P, N])
          (fun row : BHist =>
            hsame row S ∨ hsame row A ∨ hsame row R ∨ hsame row N ∨
              (Cont S A publicRead ∧ Cont publicRead R namedRead))
          (fun row : BHist => hsame row N ∧ PkgSig bundle N pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro N ⟨hsame_refl N, fields⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inl source.left)))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, pkgSig⟩
    }
  exact ⟨cert, fields, sourceAccess, publicNamed, pkgSig⟩

end BEDC.Derived.OnticStateUp
