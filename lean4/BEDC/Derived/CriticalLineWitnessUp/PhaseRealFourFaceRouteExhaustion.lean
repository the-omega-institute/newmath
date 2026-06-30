import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_phase_real_four_face_route_exhaustion
    {Z S M R Q H C P N dyadicFace streamFace regseqFace realFace completionRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S dyadicFace ->
        Cont dyadicFace Q streamFace ->
          Cont streamFace R regseqFace ->
            Cont regseqFace H realFace ->
              Cont realFace N completionRead ->
                SemanticNameCert
                    (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row completionRead ∧ Cont Z S dyadicFace ∧
                        Cont dyadicFace Q streamFace)
                    (fun row : BHist =>
                      hsame row completionRead ∧ Cont streamFace R regseqFace ∧
                        Cont regseqFace H realFace ∧ Cont realFace N completionRead)
                    hsame ∧
                  UnaryHistory dyadicFace ∧ UnaryHistory streamFace ∧
                    UnaryHistory regseqFace ∧ UnaryHistory realFace ∧
                      UnaryHistory completionRead ∧ hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet dyadicRoute streamRoute regseqRoute realRoute completionRoute
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
  have dyadicUnary : UnaryHistory dyadicFace :=
    unary_cont_closed unaryZ unaryS dyadicRoute
  have streamUnary : UnaryHistory streamFace :=
    unary_cont_closed dyadicUnary unaryQ streamRoute
  have regseqUnary : UnaryHistory regseqFace :=
    unary_cont_closed streamUnary unaryR regseqRoute
  have realUnary : UnaryHistory realFace :=
    unary_cont_closed regseqUnary unaryH realRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed realUnary unaryN completionRoute
  have sourceAtCompletion : hsame completionRead completionRead ∧ UnaryHistory completionRead :=
    ⟨hsame_refl completionRead, completionUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row completionRead ∧ Cont Z S dyadicFace ∧
              Cont dyadicFace Q streamFace)
          (fun row : BHist =>
            hsame row completionRead ∧ Cont streamFace R regseqFace ∧
              Cont regseqFace H realFace ∧ Cont realFace N completionRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro completionRead sourceAtCompletion
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
      exact ⟨source.left, dyadicRoute, streamRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, regseqRoute, realRoute, completionRoute⟩
  }
  exact
    ⟨cert, dyadicUnary, streamUnary, regseqUnary, realUnary, completionUnary, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
