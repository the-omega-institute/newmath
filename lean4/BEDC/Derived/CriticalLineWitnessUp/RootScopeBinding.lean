import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_scope_binding_certificate
    {Z S M R Q H C P N publicRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont (append Z S) Q publicRead ->
        SemanticNameCert
            (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
            (fun row : BHist => hsame row publicRead)
            (fun row : BHist => hsame row publicRead ∧ Cont (append Z S) Q publicRead)
            hsame ∧
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory H ∧
            UnaryHistory publicRead ∧ hsame H (append Z S) ∧ Cont M R Q ∧ Cont Q H C ∧
              Cont C P N ∧ Cont (append Z S) Q publicRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet publicRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryAppend : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport unaryAppend (hsame_symm sameH)
  have unaryPublicRead : UnaryHistory publicRead :=
    unary_cont_closed unaryAppend unaryQ publicRoute
  have sourceAtPublicRead : hsame publicRead publicRead ∧ UnaryHistory publicRead :=
    ⟨hsame_refl publicRead, unaryPublicRead⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row publicRead)
          (fun row : BHist => hsame row publicRead ∧ Cont (append Z S) Q publicRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourceAtPublicRead
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, publicRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryQ, unaryH, unaryPublicRead, sameH, routeQ, routeC, routeN,
      publicRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
