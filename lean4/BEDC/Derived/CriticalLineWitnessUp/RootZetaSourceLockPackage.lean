import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_zeta_source_lock_package
    {Z S M R Q H C P N zetaRead sourceLock : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zetaRead ->
        Cont zetaRead Q sourceLock ->
          SemanticNameCert
              (fun row : BHist => hsame row sourceLock /\ UnaryHistory row)
              (fun row : BHist =>
                hsame row Z \/ hsame row S \/ hsame row M \/ hsame row Q \/
                  hsame row sourceLock)
              (fun row : BHist =>
                UnaryHistory row /\ Cont Z S zetaRead /\ Cont zetaRead Q sourceLock /\
                  hsame H (append Z S))
              hsame /\
            UnaryHistory zetaRead /\ UnaryHistory sourceLock := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zetaRoute sourceLockRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, _routeC, _routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have zetaUnary : UnaryHistory zetaRead :=
    unary_cont_closed unaryZ unaryS zetaRoute
  have sourceLockUnary : UnaryHistory sourceLock :=
    unary_cont_closed zetaUnary unaryQ sourceLockRoute
  have sourceAtLock : hsame sourceLock sourceLock /\ UnaryHistory sourceLock :=
    ⟨hsame_refl sourceLock, sourceLockUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sourceLock /\ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z \/ hsame row S \/ hsame row M \/ hsame row Q \/
              hsame row sourceLock)
          (fun row : BHist =>
            UnaryHistory row /\ Cont Z S zetaRead /\ Cont zetaRead Q sourceLock /\
              hsame H (append Z S))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sourceLock sourceAtLock
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, zetaRoute, sourceLockRoute, sameH⟩
  }
  exact ⟨cert, zetaUnary, sourceLockUnary⟩

end BEDC.Derived.CriticalLineWitnessUp
