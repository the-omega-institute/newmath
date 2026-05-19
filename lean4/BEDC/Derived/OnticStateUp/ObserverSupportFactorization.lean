import BEDC.Derived.OnticStateUp.TasteGate
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

theorem OnticStateObserverSupportFactorization [AskSetup] [PackageSetup]
    {S A K R H C P N observerRead supportRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont S A observerRead →
      Cont observerRead R supportRead →
        Cont supportRead N publicRead →
          PkgSig bundle publicRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  hsame row publicRead ∧
                    FieldFaithful.fields (OnticStateUp.mk S A K R H C P N) =
                      [S, A, K, R, H, C, P, N])
                (fun row : BHist =>
                  hsame row A ∨ hsame row K ∨ hsame row R ∨
                    (Cont S A observerRead ∧ Cont observerRead R supportRead))
                (fun row : BHist => hsame row publicRead ∧ PkgSig bundle publicRead pkg)
                hsame ∧
              FieldFaithful.fields (OnticStateUp.mk S A K R H C P N) =
                  [S, A, K, R, H, C, P, N] ∧
                Cont S A observerRead ∧ Cont observerRead R supportRead ∧
                  Cont supportRead N publicRead ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame FieldFaithful SemanticNameCert
  intro observerRoute supportRoute publicRoute publicPkg
  have fieldsExact :
      FieldFaithful.fields (OnticStateUp.mk S A K R H C P N) =
        [S, A, K, R, H, C, P, N] := by
    rfl
  have sourceAtPublic :
      (fun row : BHist =>
        hsame row publicRead ∧
          FieldFaithful.fields (OnticStateUp.mk S A K R H C P N) =
            [S, A, K, R, H, C, P, N]) publicRead := by
    exact ⟨hsame_refl publicRead, fieldsExact⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row publicRead ∧
              FieldFaithful.fields (OnticStateUp.mk S A K R H C P N) =
                [S, A, K, R, H, C, P, N])
          (fun row : BHist =>
            hsame row A ∨ hsame row K ∨ hsame row R ∨
              (Cont S A observerRead ∧ Cont observerRead R supportRead))
          (fun row : BHist => hsame row publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourceAtPublic
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row _source
      exact Or.inr (Or.inr (Or.inr ⟨observerRoute, supportRoute⟩))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, publicPkg⟩
  }
  exact ⟨cert, fieldsExact, observerRoute, supportRoute, publicRoute, publicPkg⟩

end BEDC.Derived.OnticStateUp
