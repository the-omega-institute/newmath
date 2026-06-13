import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_zero_refusal_locality
    {Z S M R Q H C P N zeroRead refusalRead replay : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont Z S zeroRead →
        Cont zeroRead Q refusalRead →
          Cont H C replay →
            SemanticNameCert
                (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
                (fun row : BHist => hsame row refusalRead)
                (fun row : BHist =>
                  hsame row refusalRead ∧ Cont zeroRead Q refusalRead ∧ Cont H C replay)
                hsame ∧
              UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory zeroRead ∧
                UnaryHistory refusalRead ∧ UnaryHistory replay ∧ hsame H (append Z S) ∧
                  Cont Z S zeroRead ∧ Cont zeroRead Q refusalRead ∧ Cont H C replay ∧
                    Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zeroRoute refusalRoute replayRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed unaryZ unaryS zeroRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed zeroUnary unaryQ refusalRoute
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed unaryH unaryC replayRoute
  have sourceAtRefusal : hsame refusalRead refusalRead ∧ UnaryHistory refusalRead :=
    ⟨hsame_refl refusalRead, refusalUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row refusalRead)
          (fun row : BHist =>
            hsame row refusalRead ∧ Cont zeroRead Q refusalRead ∧ Cont H C replay)
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, refusalRoute, replayRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryQ, zeroUnary, refusalUnary, replayUnary, sameH, zeroRoute,
      refusalRoute, replayRoute, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
