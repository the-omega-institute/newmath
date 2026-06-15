import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_public_export {Z S M R Q H C P N : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      UnaryHistory (append Z S) ∧ UnaryHistory Q ∧ hsame H (append Z S) ∧
        Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have sourceUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have qUnary : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  exact ⟨sourceUnary, qUnary, sameH, routeQ, routeC, routeN⟩

theorem CriticalLineWitnessCarrier_public_export_certificate
    {Z S M R Q H C P N publicRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Q H publicRead ->
        SemanticNameCert
            (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q ∨
                hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                  hsame row publicRead)
            (fun row : BHist =>
              UnaryHistory row ∧ Cont Q H publicRead ∧ Cont M R Q ∧ Cont Q H C ∧
                Cont C P N)
            hsame ∧
          UnaryHistory publicRead ∧ hsame H (append Z S) ∧ Cont M R Q ∧
            Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet publicRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have sourceUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport sourceUnary (hsame_symm sameH)
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed unaryQ unaryH publicRoute
  have sourceAtPublic : hsame publicRead publicRead ∧ UnaryHistory publicRead :=
    ⟨hsame_refl publicRead, publicUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q H publicRead ∧ Cont M R Q ∧ Cont Q H C ∧
              Cont C P N)
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
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, publicRoute, routeQ, routeC, routeN⟩
  }
  exact ⟨cert, publicUnary, sameH, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
