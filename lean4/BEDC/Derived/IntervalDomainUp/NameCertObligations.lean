import BEDC.Derived.IntervalDomainUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.IntervalDomainUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem IntervalDomainNameCertObligations
    {L R N W Q E H C P A refinementRead directedRead endpointRead sealRead : BHist} :
    Cont L R refinementRead ->
      Cont refinementRead N directedRead ->
        Cont W Q endpointRead ->
          Cont directedRead endpointRead sealRead ->
            hsame H A ->
              SemanticNameCert
                  (fun row : BHist => hsame row sealRead ∧
                    (hsame row E ∨ hsame row sealRead))
                  (fun row : BHist =>
                    hsame row L ∨ hsame row R ∨ hsame row N ∨ hsame row W ∨
                      hsame row Q ∨ hsame row E ∨ hsame row sealRead)
                  (fun _row : BHist => Cont directedRead endpointRead sealRead ∧
                    hsame H A)
                  hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert NameCert
  intro _refinementRoute _directedRoute _endpointRoute sealRoute structuralSame
  have sourceSeal :
      (fun row : BHist => hsame row sealRead ∧ (hsame row E ∨ hsame row sealRead))
        sealRead := by
    exact ⟨hsame_refl sealRead, Or.inr (hsame_refl sealRead)⟩
  exact {
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
            Or.inr (hsame_trans (hsame_symm sameRows) source.left)⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row _source
      exact ⟨sealRoute, structuralSame⟩
  }

theorem IntervalDomainRealSealNonescape
    {L R N W Q E H C P A sealRead : BHist} :
    Cont L R N ->
      Cont N W Q ->
        Cont W Q E ->
          Cont Q E sealRead ->
            hsame H A ->
              SemanticNameCert
                  (fun row : BHist => hsame row sealRead ∧
                    (hsame row E ∨ hsame row Q ∨ hsame row sealRead))
                  (fun row : BHist =>
                    hsame row L ∨ hsame row R ∨ hsame row N ∨ hsame row W ∨
                      hsame row Q ∨ hsame row E ∨ hsame row sealRead)
                  (fun _row : BHist => Cont Q E sealRead ∧ hsame H A)
                  hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert NameCert
  intro _locatedRoute _windowRoute _realRoute sealRoute structuralSame
  have sourceSeal :
      (fun row : BHist => hsame row sealRead ∧
        (hsame row E ∨ hsame row Q ∨ hsame row sealRead)) sealRead := by
    exact ⟨hsame_refl sealRead, Or.inr (Or.inr (hsame_refl sealRead))⟩
  exact {
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
            Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) source.left))⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row _source
      exact ⟨sealRoute, structuralSame⟩
  }

theorem IntervalDomainRegularCauchyDirectedWidth
    {L R N W Q E H C P A widthRead directedRead readbackRead sealRead : BHist} :
    UnaryHistory R →
      UnaryHistory N →
        UnaryHistory W →
          UnaryHistory Q →
            UnaryHistory E →
              Cont R N widthRead →
                Cont widthRead W directedRead →
                  Cont directedRead Q readbackRead →
                    Cont readbackRead E sealRead →
                      hsame H A →
                        IntervalDomainTasteGate_single_carrier_alignment_fields
                            (IntervalDomainUp.mk L R N W Q E H C P A) =
                          [L, R, N, W, Q, E, H, C, P, A] ∧
                          SemanticNameCert
                              (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row R ∨ hsame row N ∨ hsame row W ∨
                                  hsame row Q ∨ hsame row E ∨ hsame row sealRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont R N widthRead ∧
                                  Cont widthRead W directedRead ∧
                                    Cont directedRead Q readbackRead ∧
                                      Cont readbackRead E sealRead ∧ hsame H A)
                              hsame ∧
                            UnaryHistory widthRead ∧ UnaryHistory directedRead ∧
                              UnaryHistory readbackRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert NameCert
  intro hR hN hW hQ hE widthRoute directedRoute readbackRoute sealRoute structuralSame
  have hWidth : UnaryHistory widthRead := unary_cont_closed hR hN widthRoute
  have hDirected : UnaryHistory directedRead := unary_cont_closed hWidth hW directedRoute
  have hReadback : UnaryHistory readbackRead := unary_cont_closed hDirected hQ readbackRoute
  have hSeal : UnaryHistory sealRead := unary_cont_closed hReadback hE sealRoute
  have sourceSeal : hsame sealRead sealRead ∧ UnaryHistory sealRead :=
    ⟨hsame_refl sealRead, hSeal⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row N ∨ hsame row W ∨ hsame row Q ∨
              hsame row E ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R N widthRead ∧
              Cont widthRead W directedRead ∧ Cont directedRead Q readbackRead ∧
                Cont readbackRead E sealRead ∧ hsame H A)
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, widthRoute, directedRoute, readbackRoute, sealRoute, structuralSame⟩
  }
  exact ⟨rfl, cert, hWidth, hDirected, hReadback, hSeal⟩

end BEDC.Derived.IntervalDomainUp
