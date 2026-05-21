import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_signature_gap_nonescape
    {Z S M R Q H C P N signatureRead gapRead readback refusalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z H signatureRead ->
        Cont signatureRead Q gapRead ->
          Cont gapRead N readback ->
            Cont readback Q refusalRead ->
              SemanticNameCert
                  (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row refusalRead ∧ Cont Z H signatureRead ∧
                      Cont signatureRead Q gapRead)
                  (fun row : BHist =>
                    hsame row refusalRead ∧ Cont readback Q refusalRead)
                  hsame ∧
                UnaryHistory signatureRead ∧ UnaryHistory gapRead ∧
                  UnaryHistory readback ∧ UnaryHistory refusalRead ∧
                    hsame H (append Z S) ∧ Cont M R Q ∧ Cont Q H C ∧
                      Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet signatureRoute gapRoute readbackRoute refusalRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryRoot : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport unaryRoot (hsame_symm sameH)
  have signatureUnary : UnaryHistory signatureRead :=
    unary_cont_closed unaryZ unaryH signatureRoute
  have gapUnary : UnaryHistory gapRead :=
    unary_cont_closed signatureUnary unaryQ gapRoute
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed gapUnary unaryN readbackRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed readbackUnary unaryQ refusalRoute
  have sourceAtRefusal : hsame refusalRead refusalRead ∧ UnaryHistory refusalRead :=
    ⟨hsame_refl refusalRead, refusalUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row refusalRead ∧ Cont Z H signatureRead ∧ Cont signatureRead Q gapRead)
          (fun row : BHist =>
            hsame row refusalRead ∧ Cont readback Q refusalRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro refusalRead sourceAtRefusal
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
      exact ⟨source.left, signatureRoute, gapRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, refusalRoute⟩
  }
  exact
    ⟨cert, signatureUnary, gapUnary, readbackUnary, refusalUnary, sameH, routeQ, routeC,
      routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
