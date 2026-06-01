import BEDC.Derived.LocatedLimitUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatedLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedLimitWindowScheduleExactness [AskSetup] [PackageSetup]
    {S M T Q E H C P N scheduleRead readbackRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont S M scheduleRead →
      Cont scheduleRead T readbackRead →
        PkgSig bundle P pkg →
          UnaryHistory S →
            UnaryHistory M →
              UnaryHistory T →
                SemanticNameCert
                    (fun row : BHist =>
                      (hsame row scheduleRead ∨ hsame row readbackRead) ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row S ∨ hsame row M ∨ hsame row T ∨ hsame row Q ∨
                        hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                          hsame row N ∨ hsame row scheduleRead ∨ hsame row readbackRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont S M scheduleRead ∧
                        Cont scheduleRead T readbackRead ∧ PkgSig bundle P pkg)
                    hsame ∧
                  UnaryHistory scheduleRead ∧ UnaryHistory readbackRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro scheduleCont readbackCont pkgP unaryS unaryM unaryT
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed unaryS unaryM scheduleCont
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed scheduleUnary unaryT readbackCont
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row scheduleRead ∨ hsame row readbackRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row M ∨ hsame row T ∨ hsame row Q ∨ hsame row E ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row scheduleRead ∨ hsame row readbackRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S M scheduleRead ∧ Cont scheduleRead T readbackRead ∧
              PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro scheduleRead ⟨Or.inl (hsame_refl scheduleRead), scheduleUnary⟩
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
        constructor
        · cases source.left with
          | inl sameSchedule =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameSchedule)
          | inr sameReadback =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameReadback)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameSchedule =>
          right
          right
          right
          right
          right
          right
          right
          right
          right
          exact Or.inl sameSchedule
      | inr sameReadback =>
          right
          right
          right
          right
          right
          right
          right
          right
          right
          exact Or.inr sameReadback
    ledger_sound := by
      intro _row source
      exact ⟨source.right, scheduleCont, readbackCont, pkgP⟩
  }
  exact ⟨cert, scheduleUnary, readbackUnary⟩

end BEDC.Derived.LocatedLimitUp
