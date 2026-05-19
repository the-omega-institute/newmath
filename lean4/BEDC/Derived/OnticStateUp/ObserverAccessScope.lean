import BEDC.Derived.OnticStateUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.OnticStateUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.Meta.TasteGate

theorem OnticStateObserverAccessScope
    {S A K R H C P N observerRead classifierRead residueRead : BHist} :
    Cont S A observerRead ->
      Cont observerRead K classifierRead ->
        Cont A R residueRead ->
          SemanticNameCert
              (fun row : BHist =>
                hsame row classifierRead ∧
                  FieldFaithful.fields (OnticStateUp.mk S A K R H C P N) =
                    [S, A, K, R, H, C, P, N])
              (fun row : BHist => hsame row classifierRead)
              (fun row : BHist => hsame row classifierRead ∧ Cont observerRead K classifierRead)
              hsame ∧
            FieldFaithful.fields (OnticStateUp.mk S A K R H C P N) =
                [S, A, K, R, H, C, P, N] ∧
              onticStateFromEventFlow (onticStateToEventFlow
                  (OnticStateUp.mk S A K R H C P N)) =
                some (OnticStateUp.mk S A K R H C P N) ∧
                hsame A A ∧ hsame K K ∧ hsame R R ∧ Cont S A observerRead ∧
                  Cont observerRead K classifierRead ∧ Cont A R residueRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame FieldFaithful SemanticNameCert
  intro observerRoute classifierRoute residueRoute
  have fieldsExact :
      FieldFaithful.fields (OnticStateUp.mk S A K R H C P N) =
        [S, A, K, R, H, C, P, N] := by
    rfl
  have sourceAtClassifier :
      hsame classifierRead classifierRead ∧
        FieldFaithful.fields (OnticStateUp.mk S A K R H C P N) =
          [S, A, K, R, H, C, P, N] := by
    exact ⟨hsame_refl classifierRead, fieldsExact⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row classifierRead ∧
              FieldFaithful.fields (OnticStateUp.mk S A K R H C P N) =
                [S, A, K, R, H, C, P, N])
          (fun row : BHist => hsame row classifierRead)
          (fun row : BHist => hsame row classifierRead ∧ Cont observerRead K classifierRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro classifierRead sourceAtClassifier
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
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, classifierRoute⟩
  }
  exact
    ⟨cert, fieldsExact,
      OnticStateTasteGate_single_carrier_alignment.right.left
        (OnticStateUp.mk S A K R H C P N),
      hsame_refl A, hsame_refl K, hsame_refl R, observerRoute, classifierRoute,
      residueRoute⟩

end BEDC.Derived.OnticStateUp
