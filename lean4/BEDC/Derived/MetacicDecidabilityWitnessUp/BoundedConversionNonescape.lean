import BEDC.Derived.MetacicDecidabilityWitnessUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetacicDecidabilityWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicDecidabilityWitnessBoundedConversionNonescape [AskSetup] [PackageSetup]
    {bounded finished route provenance name boundedFinished named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    (boundedUnary : UnaryHistory bounded)
    (finishedUnary : UnaryHistory finished)
    (routeUnary : UnaryHistory route)
    (boundedFinishedRoute : Cont bounded finished boundedFinished)
    (namedRoute : Cont boundedFinished route named)
    (provenancePkg : PkgSig bundle provenance pkg)
    (localNamePkg : PkgSig bundle name pkg) :
    SemanticNameCert
        (fun row : BHist => hsame row named ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row bounded ∨ hsame row finished ∨ hsame row boundedFinished ∨
            hsame row named)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont bounded finished boundedFinished ∧
            Cont boundedFinished route named ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle name pkg)
        hsame ∧
      UnaryHistory boundedFinished ∧ UnaryHistory named := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  have boundedFinishedUnary : UnaryHistory boundedFinished :=
    unary_cont_closed boundedUnary finishedUnary boundedFinishedRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed boundedFinishedUnary routeUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row named ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row bounded ∨ hsame row finished ∨ hsame row boundedFinished ∨
              hsame row named)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont bounded finished boundedFinished ∧
              Cont boundedFinished route named ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle name pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro named ⟨hsame_refl named, namedUnary⟩
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
        exact Or.inr (Or.inr (Or.inr source.left))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, boundedFinishedRoute, namedRoute, provenancePkg, localNamePkg⟩
    }
  exact ⟨cert, boundedFinishedUnary, namedUnary⟩

end BEDC.Derived.MetacicDecidabilityWitnessUp
