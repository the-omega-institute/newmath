import BEDC.Derived.CauchyRepresentationUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.CauchyRepresentationUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CauchyRepresentationStreamRegSeqRatHandoff
    {S W R D A G H C P E N windowRead readbackRead dyadicRead sealRead representedRead : BHist} :
    UnaryHistory S → UnaryHistory W → UnaryHistory R → UnaryHistory D → UnaryHistory A →
      UnaryHistory G → Cont S W windowRead → Cont windowRead R readbackRead →
        Cont readbackRead D dyadicRead → Cont dyadicRead A sealRead →
          Cont sealRead G representedRead →
            cauchyRepresentationFields (CauchyRepresentationUp.mk S W R D A G H C P E N) =
              [S, W, R, D, A, G, H, C, P, E, N] ∧
              UnaryHistory windowRead ∧ UnaryHistory readbackRead ∧
                UnaryHistory dyadicRead ∧ UnaryHistory sealRead ∧
                  UnaryHistory representedRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro unaryS unaryW unaryR unaryD unaryA unaryG
  intro windowRoute readbackRoute dyadicRoute sealRoute representedRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed unaryS unaryW windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary unaryR readbackRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed readbackUnary unaryD dyadicRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed dyadicUnary unaryA sealRoute
  have representedUnary : UnaryHistory representedRead :=
    unary_cont_closed sealUnary unaryG representedRoute
  exact ⟨rfl, windowUnary, readbackUnary, dyadicUnary, sealUnary, representedUnary⟩

theorem CauchyRepresentationCarrier_namecert_obligations
    {S W R D A G H C P E N windowRead readbackRead dyadicRead sealRead
      representedRead : BHist} :
    UnaryHistory S ->
      UnaryHistory W ->
        UnaryHistory R ->
          UnaryHistory D ->
            UnaryHistory A ->
              UnaryHistory G ->
                Cont S W windowRead ->
                  Cont windowRead R readbackRead ->
                    Cont readbackRead D dyadicRead ->
                      Cont dyadicRead A sealRead ->
                        Cont sealRead G representedRead ->
                          SemanticNameCert
                              (fun row : BHist => hsame row representedRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row S ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨
                                  hsame row A ∨ hsame row G ∨ hsame row representedRead)
                              (fun row : BHist => UnaryHistory row ∧ Cont sealRead G representedRead)
                              hsame ∧ UnaryHistory windowRead ∧ UnaryHistory readbackRead ∧
                                UnaryHistory dyadicRead ∧ UnaryHistory sealRead ∧
                                  UnaryHistory representedRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro unaryS unaryW unaryR unaryD unaryA unaryG
  intro windowRoute readbackRoute dyadicRoute sealRoute representedRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed unaryS unaryW windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary unaryR readbackRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed readbackUnary unaryD dyadicRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed dyadicUnary unaryA sealRoute
  have representedUnary : UnaryHistory representedRead :=
    unary_cont_closed sealUnary unaryG representedRoute
  have sourceRepresented :
      (fun row : BHist => hsame row representedRead ∧ UnaryHistory row) representedRead := by
    exact ⟨hsame_refl representedRead, representedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row representedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨
              hsame row A ∨ hsame row G ∨ hsame row representedRead)
          (fun row : BHist => UnaryHistory row ∧ Cont sealRead G representedRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro representedRead sourceRepresented
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, representedRoute⟩
  }
  exact
    ⟨cert, windowUnary, readbackUnary, dyadicUnary, sealUnary, representedUnary⟩

end BEDC.Derived.CauchyRepresentationUp
