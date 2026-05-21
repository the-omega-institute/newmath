import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_source_signature_readback
    {Z S M R Q H C P N sourceRead signatureRead dependencyRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead ->
        Cont sourceRead Q signatureRead ->
          Cont signatureRead H dependencyRead ->
            SemanticNameCert
                (fun row : BHist => hsame row dependencyRead ∧ UnaryHistory row)
                (fun row : BHist => hsame row dependencyRead ∧ Cont Z S sourceRead)
                (fun row : BHist => hsame row dependencyRead ∧ Cont signatureRead H dependencyRead)
                hsame ∧
              UnaryHistory sourceRead ∧ UnaryHistory signatureRead ∧
                UnaryHistory dependencyRead ∧ hsame H (append Z S) ∧ Cont M R Q ∧
                  Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet sourceRoute signatureRoute dependencyRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have signatureUnary : UnaryHistory signatureRead :=
    unary_cont_closed sourceUnary unaryQ signatureRoute
  have appendZSUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport appendZSUnary (hsame_symm sameH)
  have dependencyUnary : UnaryHistory dependencyRead :=
    unary_cont_closed signatureUnary unaryH dependencyRoute
  have sourceAtDependency : hsame dependencyRead dependencyRead ∧ UnaryHistory dependencyRead :=
    ⟨hsame_refl dependencyRead, dependencyUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row dependencyRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row dependencyRead ∧ Cont Z S sourceRead)
          (fun row : BHist => hsame row dependencyRead ∧ Cont signatureRead H dependencyRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro dependencyRead sourceAtDependency
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
      exact ⟨source.left, sourceRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, dependencyRoute⟩
  }
  exact
    ⟨cert, sourceUnary, signatureUnary, dependencyUnary, sameH, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
