import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_classifier_separation
    {Z S M R Q H C P N zeroRead modulusRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont Z S zeroRead →
        Cont M R modulusRead →
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory zeroRead ∧
            UnaryHistory modulusRead ∧ hsame H (append Z S) ∧ Cont Z S zeroRead ∧
              Cont M R modulusRead ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet zeroRoute modulusRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed unaryZ unaryS zeroRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryM unaryR modulusRoute
  exact
    ⟨unaryZ, unaryS, unaryM, zeroUnary, modulusUnary, sameH, zeroRoute, modulusRoute,
      routeQ, routeC, routeN⟩

theorem CriticalLineWitnessCarrier_classifier_semantic_namecert
    {Z S M R Q H C P N classifierRead separatedRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Q H classifierRead ->
        Cont classifierRead N separatedRead ->
          SemanticNameCert
              (fun row : BHist => hsame row separatedRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row separatedRead ∧ Cont Q H classifierRead)
              (fun row : BHist =>
                hsame row separatedRead ∧ Cont classifierRead N separatedRead)
              hsame ∧
            UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory N ∧
              UnaryHistory classifierRead ∧ UnaryHistory separatedRead ∧
                hsame H (append Z S) ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N ∧
                  Cont Q H classifierRead ∧ Cont classifierRead N separatedRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet classifierRoute separatedRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed unaryQ unaryH classifierRoute
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed classifierUnary unaryN separatedRoute
  have sourceAtSeparated : hsame separatedRead separatedRead ∧ UnaryHistory separatedRead :=
    ⟨hsame_refl separatedRead, separatedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row separatedRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row separatedRead ∧ Cont Q H classifierRead)
          (fun row : BHist =>
            hsame row separatedRead ∧ Cont classifierRead N separatedRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro separatedRead sourceAtSeparated
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
      exact ⟨source.left, classifierRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, separatedRoute⟩
  }
  exact
    ⟨cert, unaryQ, unaryH, unaryN, classifierUnary, separatedUnary, sameH, routeQ,
      routeC, routeN, classifierRoute, separatedRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
