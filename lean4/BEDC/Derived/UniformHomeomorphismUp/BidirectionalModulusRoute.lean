import BEDC.Derived.UniformHomeomorphismUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.UniformHomeomorphismUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformHomeomorphismBidirectionalModulusRoute [AskSetup] [PackageSetup]
    {F G M N H C P L forwardModulus inverseModulus namedRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    (forwardUnary : UnaryHistory F)
    (inverseUnary : UnaryHistory G)
    (modulusUnary : UnaryHistory M)
    (inverseModulusUnary : UnaryHistory N)
    (routeUnary : UnaryHistory C)
    (forwardRoute : Cont F M forwardModulus)
    (inverseRoute : Cont G N inverseModulus)
    (bidirectional : Cont forwardModulus inverseModulus H)
    (named : Cont H C namedRoute)
    (provenancePkg : PkgSig bundle P pkg)
    (localNamePkg : PkgSig bundle L pkg) :
    SemanticNameCert
        (fun row : BHist => hsame row namedRoute ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row F ∨ hsame row G ∨ hsame row M ∨ hsame row N ∨
            hsame row forwardModulus ∨ hsame row inverseModulus ∨ hsame row H ∨
              hsame row namedRoute)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont F M forwardModulus ∧ Cont G N inverseModulus ∧
            Cont forwardModulus inverseModulus H ∧ Cont H C namedRoute ∧
              PkgSig bundle P pkg ∧ PkgSig bundle L pkg)
        hsame ∧
      UnaryHistory forwardModulus ∧ UnaryHistory inverseModulus ∧ UnaryHistory H ∧
        UnaryHistory namedRoute := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  have forwardModulusUnary : UnaryHistory forwardModulus :=
    unary_cont_closed forwardUnary modulusUnary forwardRoute
  have inverseModulusUnary' : UnaryHistory inverseModulus :=
    unary_cont_closed inverseUnary inverseModulusUnary inverseRoute
  have hUnary : UnaryHistory H :=
    unary_cont_closed forwardModulusUnary inverseModulusUnary' bidirectional
  have namedRouteUnary : UnaryHistory namedRoute :=
    unary_cont_closed hUnary routeUnary named
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRoute ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row G ∨ hsame row M ∨ hsame row N ∨
              hsame row forwardModulus ∨ hsame row inverseModulus ∨ hsame row H ∨
                hsame row namedRoute)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont F M forwardModulus ∧ Cont G N inverseModulus ∧
              Cont forwardModulus inverseModulus H ∧ Cont H C namedRoute ∧
                PkgSig bundle P pkg ∧ PkgSig bundle L pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro namedRoute
          ⟨hsame_refl namedRoute, namedRouteUnary⟩
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
        exact Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, forwardRoute, inverseRoute, bidirectional, named,
            provenancePkg, localNamePkg⟩
    }
  exact
    ⟨cert, forwardModulusUnary, inverseModulusUnary', hUnary, namedRouteUnary⟩

end BEDC.Derived.UniformHomeomorphismUp
