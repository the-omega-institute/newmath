import BEDC.Derived.RationalEmbeddingUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RationalEmbeddingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RationalEmbeddingConstantSequenceRoute [AskSetup] [PackageSetup]
    {q S R D P N qSchedule stationary dyadicSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    (qUnary : UnaryHistory q)
    (scheduleUnary : UnaryHistory S)
    (readbackUnary : UnaryHistory R)
    (dyadicUnary : UnaryHistory D)
    (qScheduleRoute : Cont q S qSchedule)
    (stationaryRoute : Cont qSchedule R stationary)
    (sealRoute : Cont stationary D dyadicSeal)
    (provenancePkg : PkgSig bundle P pkg)
    (localNamePkg : PkgSig bundle N pkg) :
    SemanticNameCert
        (fun row : BHist => hsame row dyadicSeal ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row q ∨ hsame row S ∨ hsame row R ∨ hsame row D ∨
            hsame row qSchedule ∨ hsame row stationary ∨ hsame row dyadicSeal)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont q S qSchedule ∧ Cont qSchedule R stationary ∧
            Cont stationary D dyadicSeal ∧ PkgSig bundle P pkg ∧
              PkgSig bundle N pkg)
        hsame ∧
      UnaryHistory qSchedule ∧ UnaryHistory stationary ∧ UnaryHistory dyadicSeal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  have qScheduleUnary : UnaryHistory qSchedule :=
    unary_cont_closed qUnary scheduleUnary qScheduleRoute
  have stationaryUnary : UnaryHistory stationary :=
    unary_cont_closed qScheduleUnary readbackUnary stationaryRoute
  have dyadicSealUnary : UnaryHistory dyadicSeal :=
    unary_cont_closed stationaryUnary dyadicUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row dyadicSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row q ∨ hsame row S ∨ hsame row R ∨ hsame row D ∨
              hsame row qSchedule ∨ hsame row stationary ∨ hsame row dyadicSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont q S qSchedule ∧ Cont qSchedule R stationary ∧
              Cont stationary D dyadicSeal ∧ PkgSig bundle P pkg ∧
                PkgSig bundle N pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro dyadicSeal
          ⟨hsame_refl dyadicSeal, dyadicSealUnary⟩
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
        exact
          ⟨source.right, qScheduleRoute, stationaryRoute, sealRoute, provenancePkg,
            localNamePkg⟩
    }
  exact ⟨cert, qScheduleUnary, stationaryUnary, dyadicSealUnary⟩

end BEDC.Derived.RationalEmbeddingUp
